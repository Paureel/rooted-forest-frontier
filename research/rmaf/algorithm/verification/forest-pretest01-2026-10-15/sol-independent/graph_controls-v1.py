#!/usr/bin/env python3
"""One-shot fresh prerelease instrument. No author/peer imports.

Route A: original graph deletion, BFS-path hulls, descendant clusters.
Route B: set partitions, recursive restriction, address-LCA hulls.
Exact root fixtures are calibration, never blind universal confirmation.
"""
import argparse
import collections
import hashlib
import itertools
import json
from pathlib import Path
import shutil
import signal
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent


def canon(forest):
    return tuple(sorted(tuple(sorted(block)) for block in forest))


class Graph:
    def __init__(self, tree):
        self.adj, self.label = {}, {}
        def visit(t, p):
            self.adj[p] = set()
            if type(t) is int:
                if t < 0:
                    raise ValueError("not Nat")
                self.label[p] = t
            else:
                if not isinstance(t, list) or len(t) != 2:
                    raise ValueError("not binary tree")
                for side, child in enumerate(t):
                    q = p + str(side)
                    visit(child, q)
                    self.adj[p].add(q)
                    self.adj[q].add(p)
        visit(tree, "")

    def leaves(self):
        return list(self.label.values())

    def cut(self, address):
        if not address or address not in self.adj:
            raise ValueError("root/foreign cut")
        return self.components({address})

    def components(self, removed):
        if any(not p or p not in self.adj for p in removed):
            raise ValueError("root/foreign cut")
        unseen = set(self.adj)
        blocks = []
        while unseen:
            start = min(unseen)
            todo, found = [start], set()
            while todo:
                p = todo.pop()
                if p in found:
                    continue
                found.add(p)
                for q in self.adj[p]:
                    child = p if len(p) > len(q) else q
                    if child not in removed:
                        todo.append(q)
            unseen -= found
            block = [self.label[p] for p in sorted(found) if p in self.label]
            if block:
                blocks.append(block)
        return blocks

    def path(self, a, b):
        todo = collections.deque([a])
        prev = {a: None}
        while todo:
            p = todo.popleft()
            if p == b:
                out = {p}
                while prev[p] is not None:
                    p = prev[p]
                    out.add(p)
                return out
            for q in self.adj[p]:
                if q not in prev:
                    prev[q] = p
                    todo.append(q)
        raise AssertionError("disconnected tree")

    def hull(self, block, suppress_unary=False):
        selected = [p for p, x in self.label.items() if x in block]
        if not selected:
            return set()
        out = set(selected)
        for p in selected[1:]:
            out |= self.path(selected[0], p)
        if suppress_unary:
            # Incorrect control: delete original degree-two path vertices.
            branching = {p for p in out if sum(q in out for q in self.adj[p]) >= 3}
            root = min(out, key=lambda p: (len(p), p))
            out = set(selected) | branching | {root}
        return out

    def clusters(self, block):
        selected = set(block)
        clusters = set()
        for p in self.adj:
            d = frozenset(x for q, x in self.label.items() if q.startswith(p) and x in selected)
            if 1 < len(d) < len(selected):
                clusters.add(d)
        return clusters


def a_proper(T, ss):
    labels = [] if T is None else Graph(T).leaves()
    all_source = [x for s in ss for x in Graph(s).leaves()]
    return len(set(labels)) == len(labels) and sorted(labels) == sorted(all_source)


def a_valid(T, ss, forest, skip_target=False, bad_target=False, bad_source=False):
    if not a_proper(T, ss):
        return False
    target = None if T is None else Graph(T)
    labels = [] if target is None else target.leaves()
    flat = [x for b in forest for x in b]
    if any(not b for b in forest) or sorted(flat) != sorted(labels):
        return False
    sources = [Graph(s) for s in ss]
    if any(not any(set(b) <= set(s.leaves()) for s in sources) for b in forest):
        return False
    if target is None:
        return forest == []
    if not skip_target:
        hulls = [target.hull(b, bad_target) for b in forest]
        if any(hulls[i] & hulls[j] for i in range(len(hulls)) for j in range(i)):
            return False
    for source in sources:
        family = [b for b in forest if set(b) <= set(source.leaves())]
        if sorted(x for b in family for x in b) != sorted(source.leaves()):
            return False
        if any(source.clusters(b) != target.clusters(b) for b in family):
            return False
        hulls = [source.hull(b, bad_source) for b in family]
        if any(hulls[i] & hulls[j] for i in range(len(hulls)) for j in range(i)):
            return False
    return True


def a_candidates(ss, omit=None):
    graphs = [Graph(s) for s in ss]
    unchanged = [g.leaves() for g in graphs]
    out = [(None, unchanged)]
    for i, g in enumerate(graphs):
        for edge in sorted(p for p in g.adj if p):
            if omit == (i, edge):
                continue
            out.append(((i, edge), unchanged[:i] + g.cut(edge) + unchanged[i+1:]))
    return out


# Route B does not invoke Graph, A's validity, cuts, clusters, or BFS paths.
def b_leaves(t):
    if type(t) is int:
        return [t]
    return b_leaves(t[0]) + b_leaves(t[1])


def b_proper(T, ss):
    universe = [] if T is None else b_leaves(T)
    cover = [x for s in ss for x in b_leaves(s)]
    return (all(x >= 0 for x in universe + cover)
            and len(universe) == len(set(universe))
            and collections.Counter(universe) == collections.Counter(cover))


def b_restrict(t, block):
    if type(t) is int:
        return ("leaf", t) if t in block else None
    left, right = b_restrict(t[0], block), b_restrict(t[1], block)
    if left is None:
        return right
    if right is None:
        return left
    return ("node",) + tuple(sorted((left, right)))


def b_hull(t, block):
    addresses = []
    def descend(u, path):
        if type(u) is int:
            if u in block:
                addresses.append(path)
        else:
            descend(u[0], path + "0")
            descend(u[1], path + "1")
    descend(t, "")
    if not addresses:
        return set()
    common = addresses[0]
    for address in addresses[1:]:
        while not address.startswith(common):
            common = common[:-1]
    return {address[:i] for address in addresses for i in range(len(common), len(address)+1)}


def b_disjoint(t, family):
    seen = set()
    for block in family:
        hull = b_hull(t, block)
        if seen.intersection(hull):
            return False
        seen.update(hull)
    return True


def b_valid(T, ss, forest):
    if not b_proper(T, ss):
        return False
    labels = [] if T is None else b_leaves(T)
    if any(len(b) == 0 for b in forest):
        return False
    flattened = [x for b in forest for x in b]
    if any(flattened.count(x) != 1 for x in labels) or any(x not in labels for x in flattened):
        return False
    for block in forest:
        if not any(all(x in b_leaves(s) for x in block) for s in ss):
            return False
    if T is None:
        return not forest
    if not b_disjoint(T, forest):
        return False
    for source in ss:
        universe = b_leaves(source)
        family = [block for block in forest if all(x in universe for x in block)]
        if collections.Counter(x for block in family for x in block) != collections.Counter(universe):
            return False
        for block in family:
            if b_restrict(T, block) != b_restrict(source, block):
                return False
        if not b_disjoint(source, family):
            return False
    return True


def b_partitions(labels):
    if not labels:
        yield []
        return
    first, *tail = labels
    for rest in b_partitions(tail):
        yield [[first]] + [list(b) for b in rest]
        for i in range(len(rest)):
            yield [([first] + b if j == i else list(b)) for j, b in enumerate(rest)]


def mirror(t):
    return t if type(t) is int else [mirror(t[1]), mirror(t[0])]


LARGE = [0, 17, 2**200+19, 10**80+7, 2**127+1]


def relabel(t):
    return LARGE[t] if type(t) is int else [relabel(t[0]), relabel(t[1])]


def run_case(case, variant="base"):
    start = time.perf_counter()
    T, ss = case["T"], case["ss"]
    check = lambda condition, detail: require(condition, case["id"] + ":" + variant + ":" + detail)
    check(a_proper(T, ss) == b_proper(T, ss) == case["proper"], "proper")
    candidates = a_candidates(ss)
    if "candidate_count" in case:
        check(len(candidates) == case["candidate_count"], "candidate count")
    if not case["proper"]:
        return {"id":case["id"], "variant":variant, "proper":False, "decision":"refused",
                "seconds":time.perf_counter()-start}
    labels = [] if T is None else b_leaves(T)
    check(len(candidates) <= 1 + 2*len(labels), "qualified bound")
    source_edges = sum(len(Graph(s).adj)-1 for s in ss)
    check(len(candidates) == 1 + source_edges, "exact edge count")
    all_partitions = list(b_partitions(labels))
    actual = [p for p in all_partitions if b_valid(T, ss, p)]
    check(bool(actual), "actual nonempty")
    minimum = min(max(0, len(p)-len(ss)) for p in actual)
    valid = [(e,p) for e,p in candidates if a_valid(T, ss, p)]
    cheap = {canon(p) for p in actual if max(0,len(p)-len(ss)) <= 1}
    generated = {canon(p) for _,p in valid}
    check(cheap == generated, "specific cheap coverage")
    for _, p in candidates:
        check(a_valid(T, ss, p) == b_valid(T, ss, p), "candidate full predicate")
    decision = "found" if valid else "rejected"
    check(bool(valid) == (minimum <= 1), "global cheap decision")
    if valid:
        check(min(len(p)-len(ss) for _,p in valid) == minimum, "global minimum")
    if "minimum" in case:
        check(minimum == case["minimum"], "hand minimum")
    if "valid_candidate_entries" in case:
        check(len(valid) == case["valid_candidate_entries"], "repeated valid entries")
        check(len(generated) == case["valid_candidate_distinct"], "distinct valid partitions")
    if "witness" in case:
        w = case["witness"]
        check(b_valid(T, ss, w) and a_valid(T, ss, w), "hand witness")
        check(b_valid(T, ss, [list(reversed(b)) for b in reversed(w)]), "inner outer permutations")
    if "invalid_witness" in case:
        check(not b_valid(T, ss, case["invalid_witness"]), "invalid hand witness")
    return {"id":case["id"], "variant":variant, "proper":True, "decision":decision,
            "minimum":minimum, "partitions_tested":len(all_partitions),
            "valid_actual":len(actual), "candidates":len(candidates), "valid_entries":len(valid),
            "distinct_cheap":len(generated), "cheap_partitions":[list(map(list,p)) for p in sorted(cheap)],
            "seconds":time.perf_counter()-start}


def require(condition, detail):
    if not condition:
        raise AssertionError(detail)


def corruption_controls(cases):
    by_id = {c["id"]:c for c in cases}
    events = []
    def caught(name, clean, corrupt, detail):
        require(clean, name+": clean twin failed")
        require(corrupt, name+": corruption escaped")
        events.append({"id":name,"clean_twin":True,"corruption_caught":True,"detail":detail})
    c = by_id["specific_coverage"]
    good = {canon(p) for _,p in a_candidates(c["ss"]) if a_valid(c["T"],c["ss"],p)}
    bad = {canon(p) for _,p in a_candidates(c["ss"],(0,"00")) if a_valid(c["T"],c["ss"],p)}
    witness = canon(c["witness"])
    caught("missing_specific_edge", witness in good, good-bad == {witness} and witness not in bad,
           {"missing":list(map(list,witness)),"minimum_survives":min(len(p)-1 for p in bad)==0})
    c = by_id["crossed_forest"]
    w = c["witness"]
    caught("ordinary_vs_prepaid", len(w)-len(c["ss"])==1, len(w)-1==2,
           {"prepaid":len(w)-len(c["ss"]),"ordinary":len(w)-1})
    c = by_id["crossed_single"]
    good = [p for _,p in a_candidates(c["ss"]) if a_valid(c["T"],c["ss"],p)]
    bad = [p for _,p in a_candidates(c["ss"]) if a_valid(c["T"],c["ss"],p,skip_target=True)]
    caught("false_cheap_without_target_hulls", not good, bool(bad) and min(len(p)-1 for p in bad)==1,
           {"false_witness":bad[0]})
    for kind in ("target", "source"):
        c=by_id["hidden_"+kind]
        w=c["invalid_witness"]
        kwargs={"bad_"+kind:True}
        tree = c["T"] if kind=="target" else c["ss"][0]
        overlap=sorted(Graph(tree).hull(w[0]) & Graph(tree).hull(w[1]))
        caught("hidden_"+kind+"_vertices", not a_valid(c["T"],c["ss"],w),
               a_valid(c["T"],c["ss"],w,**kwargs) and overlap==c["hidden_intersection"],
               {"original_intersection":overlap,"false_witness":w})
    g=Graph([[0,1],2])
    for address in ("", "00000"):
        refused=False
        try:
            g.cut(address)
        except ValueError:
            refused=True
        caught("invalid_cut_"+(address or "ROOT"), bool(g.cut("00")), refused,
               {"address":address})
    c=by_id["crossed_forest"]
    T,ss,w=c["T"],c["ss"],c["witness"]
    corruptions={"duplicate_label":[[0],[0],[2],[1,3]],"missing_label":[[0],[1,3]],
                 "foreign_label":[[0],[2],[1,3],[999]],"empty_block":w+[[]],
                 "mixed_source":[[0,1],[2],[3]],"root_cut_injection":[[0,2],[],[1,3]]}
    for name,p in corruptions.items():
        caught(name, a_valid(T,ss,w) and b_valid(T,ss,w),
               not a_valid(T,ss,p) and not b_valid(T,ss,p), {"corrupt":p})
    caught("comparator_mismatch",canon([[0],[1,2]])==canon([[2,1],[0]]),
           canon([[0],[1,2]])!=canon([[1],[0,2]]),{})
    return events


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--pilot",action="store_true")
    parser.add_argument("--out",required=True)
    args=parser.parse_args()
    started=time.perf_counter()
    free=shutil.disk_usage(HERE).free
    require(free >= 3*2**30,"disk floor before run")
    signal.signal(signal.SIGALRM,lambda *_: (_ for _ in ()).throw(TimeoutError("30 second cap")))
    signal.alarm(30)
    source=HERE/"fixtures-v1.json"
    fixture=json.loads(source.read_text())
    result={"phase":"prerelease","fixture_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
            "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "runtime":sys.version,"pilot":args.pilot,"disk_free_before":free,"cases":[],"corruptions":[]}
    try:
        cases=fixture["cases"]
        selected=[c for c in cases if c["id"] in ("singleton","crossed_forest")] if args.pilot else cases
        for c in selected:
            result["cases"].append(run_case(c))
        if not args.pilot:
            result["corruptions"]=corruption_controls(cases)
            for c in cases:
                if c["proper"]:
                    for variant in ("mirror_permute", "large_nat"):
                        changed=dict(c)
                        if variant=="mirror_permute":
                            changed["T"]=None if c["T"] is None else mirror(c["T"])
                            changed["ss"]=[mirror(s) for s in reversed(c["ss"])]
                        else:
                            changed["T"]=None if c["T"] is None else relabel(c["T"])
                            changed["ss"]=[relabel(s) for s in c["ss"]]
                            for key in ("witness","invalid_witness"):
                                if key in c:
                                    changed[key]=[[LARGE[x] for x in b] for b in c[key]]
                        result["cases"].append(run_case(changed,variant))
        result["status"]="PASS"
    except BaseException:
        result["status"]="FAIL"
        result["failure"]=traceback.format_exc()
    finally:
        result["seconds"]=time.perf_counter()-started
        result["disk_free_after"]=shutil.disk_usage(HERE).free
        if result["disk_free_after"]<3*2**30:
            result["status"]="FAIL"
            result["resource_failure"]="disk floor after run"
        out=Path(args.out)
        require(not out.exists(),"refuse evidence overwrite")
        out.write_text(json.dumps(result,indent=2)+"\n")
        print(json.dumps({k:result[k] for k in ("status","pilot","seconds","disk_free_after")}
                         | {"case_records":len(result["cases"]),"corruptions":len(result["corruptions"]),"receipt":str(out)}))
    return 0 if result["status"]=="PASS" else 1


if __name__=="__main__":
    raise SystemExit(main())
