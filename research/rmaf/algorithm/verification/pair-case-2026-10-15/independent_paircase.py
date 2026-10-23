#!/usr/bin/env python3
"""One-shot fresh nonauthor instrument for frozen pair-case verification.

No problem-specific imports. Graph BFS hull and descendant cluster signatures
are separate routes from the literal original-RMAF recursion translations.
This instrument produces bounded evidence, never a universal proof verdict.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
from functools import lru_cache
from itertools import combinations, product
import hashlib
import json
from pathlib import Path
import time
import traceback


def frozen_tree(x):
    return tuple(frozen_tree(y) for y in x) if isinstance(x, list) else x


def canon_partition(bs):
    return tuple(sorted((tuple(sorted(b)) for b in bs), key=lambda b: (b[0], b)))


def partitions(labels):
    labels = tuple(labels)
    if not labels:
        yield ()
        return
    first, *rest = labels
    for p in partitions(rest):
        yield canon_partition(((first,),) + p)
        for i in range(len(p)):
            yield canon_partition(p[:i] + ((first,) + p[i],) + p[i + 1:])


def refines(fine, coarse):
    return all(any(set(b) <= set(c) for c in coarse) for b in fine)


def partition_check(labels, bs):
    counts = Counter(x for b in bs for x in b)
    return all(bs) and all(counts[x] == 1 for x in labels) and all(x in labels for x in counts)


class Original:
    def __init__(self, tree):
        self.tree = frozen_tree(tree)
        self.graph = {}
        self.leaf_at = {}
        self.labels = []
        def visit(t, v=""):
            self.graph.setdefault(v, set())
            if isinstance(t, int):
                self.leaf_at[v] = t
                self.labels.append(t)
            else:
                if len(t) != 2:
                    raise ValueError("Original.Tree must be binary")
                for side, child in enumerate(t):
                    w = v + str(side)
                    self.graph.setdefault(w, set()).add(v)
                    self.graph[v].add(w)
                    visit(child, w)
        visit(self.tree)
        self.edges = tuple((v[:-1], v) for v in sorted(self.graph) if v)
        self.proper = len(set(self.labels)) == len(self.labels)

    def selected_guard(self, selected):
        return self.proper and len(set(selected)) == len(selected) and set(selected) <= set(self.labels)

    def path(self, a, b):
        queue = deque([(a, (a,))])
        visited = {a}
        while queue:
            v, p = queue.popleft()
            if v == b:
                return p
            for w in sorted(self.graph[v] - visited):
                visited.add(w)
                queue.append((w, p + (w,)))
        raise AssertionError("tree disconnected")

    @lru_cache(None)
    def hull(self, selected):
        endpoints = sorted(v for v, x in self.leaf_at.items() if x in selected)
        if not endpoints:
            return frozenset()
        return frozenset(v for w in endpoints for v in self.path(endpoints[0], w))

    @lru_cache(None)
    def clusters(self, selected):
        # All selected descendant sets; unary repeats are suppressed by set.
        return frozenset(frozenset(x for w, x in self.leaf_at.items()
                                   if w.startswith(v) and x in selected)
                         for v in self.graph) - {frozenset()}

    def descendants(self, v):
        return frozenset(x for w, x in self.leaf_at.items() if w.startswith(v))

    def occupied(self, v, selected):
        occupied_neighbors = []
        for neighbor in sorted(self.graph[v]):
            seen, queue = {v, neighbor}, [neighbor]
            labels = set()
            while queue:
                w = queue.pop()
                if w in self.leaf_at:
                    labels.add(self.leaf_at[w])
                for z in self.graph[w] - seen:
                    seen.add(z)
                    queue.append(z)
            if labels & set(selected):
                occupied_neighbors.append(neighbor)
        return tuple(occupied_neighbors)

    def embedding_disjoint(self, blocks):
        hs = [self.hull(frozenset(b)) for b in blocks]
        return all(not a & b for a, b in combinations(hs, 2))

    def one_cut(self, block, sector):
        whole, color = frozenset(block), frozenset(sector)
        if not color or color == whole:
            return []
        h = self.hull(whole)
        return [e for e in self.edges if set(e) <= h and
                (self.descendants(e[1]) & whole) in (color, whole - color)]


# Fresh literal translations of the permitted original RMAF definitions.
def raw_span(t, selected):
    if isinstance(t, int):
        return {""} if t in selected else set()
    ls, rs = raw_span(t[0], selected), raw_span(t[1], selected)
    return ({""} | {"0" + v for v in ls} | {"1" + v for v in rs}) if ls or rs else set()


def raw_minimal(t, selected):
    if isinstance(t, int):
        return {""} if t in selected else set()
    ls, rs = raw_span(t[0], selected), raw_span(t[1], selected)
    if not ls:
        return {"1" + v for v in raw_minimal(t[1], selected)}
    if not rs:
        return {"0" + v for v in raw_minimal(t[0], selected)}
    return {""} | {"0" + v for v in ls} | {"1" + v for v in rs}


def raw_restrict(t, selected):
    if isinstance(t, int):
        return t if t in selected else None
    a, b = raw_restrict(t[0], selected), raw_restrict(t[1], selected)
    return b if a is None else a if b is None else (a, b)


def raw_shape(t):
    if t is None or isinstance(t, int):
        return t
    a, b = raw_shape(t[0]), raw_shape(t[1])
    return tuple(sorted((a, b), key=repr))


def agrees(s, t, blocks):
    return (partition_check(s.labels, blocks) and partition_check(t.labels, blocks)
            and all(s.clusters(frozenset(b)) == t.clusters(frozenset(b))
                    and s.clusters(frozenset(b)) for b in blocks)
            and s.embedding_disjoint(blocks) and t.embedding_disjoint(blocks))


def raw_agrees(s, t, blocks):
    return (partition_check(s.labels, blocks) and partition_check(t.labels, blocks)
            and all(raw_restrict(s.tree, b) is not None
                    and raw_restrict(t.tree, b) is not None
                    and raw_shape(raw_restrict(s.tree, b)) == raw_shape(raw_restrict(t.tree, b))
                    for b in blocks)
            and all(not (raw_minimal(s.tree, a) & raw_minimal(s.tree, b)) for a,b in combinations(blocks, 2))
            and all(not (raw_minimal(t.tree, a) & raw_minimal(t.tree, b)) for a,b in combinations(blocks, 2)))


def clear_edge(t, a, b, e):
    if e not in t.edges:
        return {"four_sectors": False, "mutual_A": False, "mutual_B": False, "eligible": False}
    a, b = frozenset(a), frozenset(b)
    d = t.descendants(e[1])
    ai, ao, bi, bo = a & d, a - d, b & d, b - d
    ha, hb = t.hull(a), t.hull(b)
    four = all((ai, ao, bi, bo))
    ca = all(not t.hull(c) & hb for c in (ai, ao))
    cb = all(not t.hull(c) & ha for c in (bi, bo))
    return {"D": sorted(d), "sectors": list(map(sorted, (ai,ao,bi,bo))),
            "four_sectors": four, "mutual_A": ca, "mutual_B": cb,
            "common_original_edge": set(e) <= ha & hb,
            "eligible": bool(four and ca and cb and set(e) <= ha & hb)}


def g_guard(t, a, b):
    return bool(t.selected_guard(a) and t.selected_guard(b) and a and b and
                not set(a) & set(b) and t.hull(frozenset(a)) & t.hull(frozenset(b)))


def exchange(a, b, d, f):
    a,b,d = set(a),set(b),set(d)
    answer = [tuple(a)]
    for block in f:
        c = set(block)
        if c <= a:
            continue
        if c <= b:
            answer.extend(tuple(x) for x in (c & d, c - d) if x)
        else:
            answer.append(tuple(c))
    return canon_partition(answer)


class Checks:
    def __init__(self):
        self.rows = []
    def equal(self, name, actual, expected):
        accepted = actual == expected
        # Exact comparator deliberately receives a different expected object.
        mutated_expected = {"deliberate_mismatch": expected}
        mutation_rejected = actual != mutated_expected
        self.rows.append({"id": name, "actual": actual, "expected": expected,
                          "passed": accepted, "mutated_expectation_rejected": mutation_rejected})
        if not accepted or not mutation_rejected:
            raise AssertionError(name)


def controls(spec, checks):
    c = spec["controls"]
    s = Original(c["identical_minimum"]["tree"])
    ps = list(partitions(s.labels))
    checks.equal("identical_partition_denominator", len(ps), 15)
    checks.equal("identical_minimum", min(map(len,(p for p in ps if agrees(s,s,p)))), 1)
    w = c["wrong_rooted_topology"]
    s,t = Original(w["left"]),Original(w["right"])
    checks.equal("wrong_rooted_topology", agrees(s,t,(tuple(s.labels),)), False)
    checks.equal("wrong_rooted_optimum", min(len(p) for p in partitions(s.labels) if agrees(s,t,p)), 2)
    s = Original(c["crossed_forest"]["tree"])
    checks.equal("crossed_forest", agrees(s,s,c["crossed_forest"]["partition"]), False)
    r = c["refinement_direction"]
    checks.equal("fine_refines",refines(r["fine"],r["coarse"]),True)
    checks.equal("coarse_does_not_refine",refines(r["coarse"],r["fine"]),False)
    r = c["suppression"]; s = Original(r["tree"])
    checks.equal("suppressed_path_original_hull",sorted(s.hull(frozenset(r["selection"]))),r["expected_hull"])
    checks.equal("displayed_not_original_edge",tuple(r["displayed_endpoints"]) in s.edges,False)
    checks.equal("displayed_original_path_length",len(s.path(*r["displayed_endpoints"]))-1,2)
    r = c["absent"]; s = Original(r["tree"])
    checks.equal("absent_raw_hull",sorted(s.hull(frozenset(r["selection"]))),[])
    checks.equal("absent_raw_restriction",raw_restrict(s.tree,r["selection"]),None)
    checks.equal("absent_guard",s.selected_guard(r["selection"]),False)
    r = c["repeated_input_labels"]; s = Original(r["tree"])
    checks.equal("repeated_tree_guard",s.proper,False)
    checks.equal("repeated_tree_raw_definition",raw_agrees(s,s,r["raw_agreement_partition"]),True)
    r = c["repeated_selection"]; s = Original(r["tree"])
    checks.equal("repeated_selection_raw_hull",sorted(s.hull(frozenset(r["selection"]))),["0"])
    checks.equal("repeated_selection_guard",s.selected_guard(r["selection"]),False)
    r = c["partition_corruptions"]
    for n in ("empty_block","repeat_label","missing_label","absent_label"):
        checks.equal(n,partition_check(r["labels"],r[n]),False)
    r = c["empty_singleton_disjoint_overlapping"]; s = Original(r["tree"])
    checks.equal("empty_hull",sorted(s.hull(frozenset())),[])
    checks.equal("singleton_hull",sorted(s.hull(frozenset([1]))),["00"])
    checks.equal("empty_G_guard",g_guard(s,[],[2,3]),False)
    checks.equal("singleton_disjoint_G_guard",g_guard(s,[1],[2]),False)
    checks.equal("overlapping_label_guard",g_guard(s,[1,2],[2,3]),False)
    r = c["boundary_orientation"]; s=Original(r["tree"])
    checks.equal("downward_descendant_color",sorted(s.descendants(r["edge"][1])),[1,2])
    checks.equal("boundary_forward_edge",tuple(r["edge"]) in s.edges,True)
    checks.equal("boundary_reversed_edge",tuple(reversed(r["edge"])) in s.edges,False)
    return {"control_denominator":len(checks.rows), "controls_passed":len(checks.rows)}


def geometry_check(t, deadline):
    labels=sorted(set(t.labels)); selections=0; degree_checks=0
    for bits in product((0,1),repeat=len(labels)):
        a=frozenset(x for x,c in zip(labels,bits) if c)
        h=t.hull(a)
        assert h == raw_minimal(t.tree,a), ("minimalVertices", a)
        for v in h:
            occupied=len(t.occupied(v,a))
            degree=sum(w in h for w in t.graph[v])
            assert occupied==degree,("actual-region-degree", a,v,occupied,degree)
            degree_checks+=1
        selections+=1
        if time.monotonic()>deadline: raise TimeoutError("geometry deadline")
    g_tested=0; g_eligible=0; three=0; edge=0
    for colors in product((0,1,2),repeat=len(labels)):
        a=tuple(x for x,c in zip(labels,colors) if c==1)
        b=tuple(x for x,c in zip(labels,colors) if c==2)
        g_tested+=1
        if not g_guard(t,a,b): continue
        g_eligible+=1
        common=t.hull(frozenset(a)) & t.hull(frozenset(b))
        witnesses=[v for v in common if len(t.occupied(v,a))==3 or len(t.occupied(v,b))==3]
        es=[e for e in t.edges if clear_edge(t,a,b,e)["eligible"]]
        assert witnesses or es,("G-in-regime-fire",a,b,sorted(common))
        three+=bool(witnesses); edge+=bool(es)
        if time.monotonic()>deadline: raise TimeoutError("G deadline")
    return {"selection_denominator":selections,"actual_region_degree_denominator":degree_checks,
            "G_assignment_denominator":g_tested,"G_guard_eligible":g_eligible,
            "G_with_three_region_witness":three,"G_with_mutual_edge_witness":edge}


def fixture(name, f, checks, cap):
    started=time.monotonic(); deadline=started+cap
    s,t=Original(f["S"]),Original(f["T"])
    assert s.proper and t.proper and set(s.labels)==set(t.labels)
    assert len(s.labels)<=7
    p=canon_partition(f["P"]); a=frozenset(f["A"]); b=frozenset(f["B"])
    assert partition_check(s.labels,p) and s.embedding_disjoint(p)
    assert s.clusters(a)==t.clusters(a)
    assert all(not t.hull(frozenset(c)) & (t.hull(a)|t.hull(b)) for c in p if set(c) not in (set(a),set(b)))
    allp=list(partitions(sorted(s.labels)))
    checks.equal(name+"_partition_denominator",len(allp),f["partition_denominator"])
    assert len(allp)==len(set(allp)),"duplicate partition generation"
    full=[]; refining=[]; raw_comparisons=0
    for q in allp:
        actual=agrees(s,t,q); raw=raw_agrees(s,t,q)
        assert actual==raw,("agreement-translation",name,q,actual,raw)
        raw_comparisons+=1
        if refines(q,p):
            refining.append(q)
            if actual: full.append(q)
        if time.monotonic()>deadline: raise TimeoutError("partition deadline")
    minimum=min(map(len,full)); kept=min(len(q) for q in full if tuple(sorted(a)) in q)
    if "refining_minimum" in f: checks.equal(name+"_refining_minimum",minimum,f["refining_minimum"])
    if "refining_A_retained_minimum" in f: checks.equal(name+"_refining_kept_minimum",kept,f["refining_A_retained_minimum"])
    common=sorted(t.hull(a)&t.hull(b))
    if "overlap_vertices" in f: checks.equal(name+"_original_overlap",common,f["overlap_vertices"])
    edges=[e for e in t.edges if clear_edge(t,a,b,e)["eligible"]]
    if "mutually_clear_edges" in f: checks.equal(name+"_mutual_edges",list(map(list,edges)),f["mutually_clear_edges"])
    e_rows=[]; exchange_denominator=0; cuts=0; exchange_rows=[]
    for e in edges:
        ed=clear_edge(t,a,b,e); d=frozenset(ed["D"])
        for q in full:
            qp=exchange(a,b,d,q)
            outside=canon_partition(c for c in q if not set(c)<=a and not set(c)<=b)
            outsidep=canon_partition(c for c in qp if not set(c)<=a and not set(c)<=b)
            conclusions={"actual_full_agreement":agrees(s,t,qp),"refines_P":refines(qp,p),
                         "A_whole":tuple(sorted(a)) in qp,
                         "all_B_sectors":all(not(set(c)&d) or not(set(c)-d) for c in qp if set(c)<=b),
                         "nonincreasing_count":len(qp)<=len(q),"outside_unchanged":outside==outsidep}
            assert all(conclusions.values()),("E-in-regime-fire",name,e,q,qp,conclusions)
            witnesses=[]
            for c in q:
                if set(c)<=b and set(c)&d and set(c)-d:
                    ws=s.one_cut(c,set(c)&d)
                    assert ws,("agreed-final-block-onecut",name,e,c)
                    witnesses.append({"agreed_final_B_block":c,"sector":sorted(set(c)&d),"original_source_edges":ws})
                    cuts+=1
            exchange_rows.append({"edge":e,"F":q,"Fprime":qp,"conclusions":conclusions,"within_final_block_source_cut_witnesses":witnesses})
            exchange_denominator+=1
        e_rows.append({"edge":e,**ed})
    if "given_F" in f:
        q=canon_partition(f["given_F"]); expected=canon_partition(f["given_Fprime"])
        checks.equal("T1_given_F_agreement",agrees(s,t,q),True)
        checks.equal("T1_given_exchange",exchange(a,b,t.descendants("00"),q),expected)
        checks.equal("T1_given_Fprime_agreement",agrees(s,t,expected),True)
        checks.equal("T1_false_whole_bad_B_onecut",bool(s.one_cut(b,{3,4})),False)
    probe=[]
    if name=="three_region_probe":
        for e in t.edges:
            ed=clear_edge(t,a,b,e)
            if not ed["four_sectors"]: continue
            d=set(ed["D"]); failed=[]; absent=[]
            for q in full:
                qp=exchange(a,b,d,q)
                if not agrees(s,t,qp): failed.append(q)
                candidates=[r for r in full if tuple(sorted(a)) in r and len(r)<=len(q)
                    and all(not(set(c)&d) or not(set(c)-d) for c in r if set(c)<=b)
                    and canon_partition(c for c in r if not set(c)<=a and not set(c)<=b)==
                        canon_partition(c for c in q if not set(c)<=a and not set(c)<=b)]
                if not candidates: absent.append(q)
            probe.append({"edge":e,**ed,"outside_binary_E":not ed["eligible"],
                          "F_denominator":len(full),"direct_construction_failures":failed,
                          "existential_failures":absent,"finite_claim_truth":not absent})
    geometry={"S":geometry_check(s,deadline),"T":geometry_check(t,deadline)}
    return {"fixture":name,"partition_denominator":len(allp),"refining_denominator":len(refining),
            "refining_agreement_denominator":len(full),"raw_definition_comparisons":raw_comparisons,
            "refining_minimum":minimum,"refining_A_retained_minimum":kept,
            "original_overlap":common,"shared_region_counts":[{"v":v,"A":len(t.occupied(v,a)),"B":len(t.occupied(v,b))} for v in common],
            "eligible_edges":e_rows,"E_F_edge_denominator":exchange_denominator,
            "final_agreed_B_cut_witness_denominator":cuts,"exchanges":exchange_rows,
            "three_region_unqualified_probe":probe,"geometry":geometry,
            "elapsed_seconds":time.monotonic()-started,"scope":"fixed finite original binary trees; universal targets OPEN"}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--spec",required=True);ap.add_argument("--mode",choices=["controls","pilot","fixtures"],required=True);ap.add_argument("--output",required=True)
    args=ap.parse_args(); output=Path(args.output)
    spec_path=Path(args.spec); spec=json.loads(spec_path.read_text()); checks=Checks()
    result={"mode":args.mode,"phase":"PRE-CANDIDATE","instrument_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),"preregistration_sha256":hashlib.sha256(spec_path.read_bytes()).hexdigest(),"scope":"readiness evidence only; G/E and main algorithm remain OPEN","started_unix":time.time()}
    status=0
    try:
        if args.mode=="controls": result["controls"]=controls(spec,checks)
        else:
            names=["binary_tiny"] if args.mode=="pilot" else ["T1","root_promoted","three_region_probe"]
            result["fixtures"]=[]
            for n in names:
                result["fixtures"].append(fixture(n,spec["fixtures"][n],checks,spec["limits"]["per_fixture_seconds"]))
                output.parent.mkdir(parents=True,exist_ok=True)
                output.write_text(json.dumps(result,indent=2)+"\n")
        result["verdict"]="BOUNDED-CHECKS-PASSED"
    except Exception as exc:
        result["verdict"]="OPEN-INSTRUMENT-OR-CASE-FAILURE";result["error"]=repr(exc);result["traceback"]=traceback.format_exc();status=1
    result["checks"]=checks.rows;result["completed_unix"]=time.time()
    output.parent.mkdir(parents=True,exist_ok=True);output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"mode":args.mode,"verdict":result["verdict"],"literal_check_denominator":len(checks.rows),"output":str(output)},sort_keys=True))
    # Dashboard evidence is emitted only after the receipt exists on disk.
    try:
        from telemetry import metric,gate,artifact
        metric("literal exact checks completed",sum(x["passed"] for x in checks.rows),total=len(checks.rows),unit="checks")
        artifact(str(output))
        if args.mode=="controls": gate("known_truth","passed" if status==0 else "failed",detail="Frozen literal controls only; receipt "+str(output))
    except ImportError: pass
    return status


if __name__=="__main__": raise SystemExit(main())
