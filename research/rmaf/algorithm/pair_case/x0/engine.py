"""One-shot bounded G/E falsifier; existing own checker lineage is disclosed.

No profile author/referee or live proof implementation is imported. Partition
enumeration is a TEST oracle and is never a production rule.
"""
import sys
from pathlib import Path
from itertools import product
from math import comb, prod
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[1]/"scaffold_adversary/coupled"))
from continuation import *


def original(raw):
    seen=[]
    def visit(x):
        if type(x) is int:
            seen.append(x)
        elif isinstance(x,(list,tuple)) and len(x)==2:
            visit(x[0]);visit(x[1])
        else:
            raise ValueError("nonbinary_or_noninteger_original")
    visit(raw)
    if len(seen)!=len(set(seen)):
        raise ValueError("repeated_original_label")
    return Graph(tree(raw))


def addresses(g,raw):
    bylabels={g.labs(v):v for v in g.ch}
    out={}
    def rec(x,p):
        labs=frozenset([x]) if type(x) is int else rec(x[0],p+"0")|rec(x[1],p+"1")
        out[p]=bylabels[labs]
        return labs
    rec(raw,"")
    return out


def occupied_regions(g,v,selected):
    adjacency={a:set() for a in g.ch}
    for a,b in g.lift:
        adjacency[a].add(b);adjacency[b].add(a)
    todo=set(g.ch)-{v};regions=[]
    while todo:
        seed=min(todo);found={seed};pending=[seed]
        while pending:
            a=pending.pop()
            for b in adjacency[a]-found-{v}:
                found.add(b);pending.append(b)
        todo-=found
        labels_=frozenset().union(*(g.group.get(w,frozenset()) for w in found))&frozenset(selected)
        if labels_:regions.append(labels_)
    return sorted(regions,key=lambda x:tuple(sorted(x)))


def edge_sectors(g,A,B,e):
    if e not in g.original_edges or e not in g.lift:
        return {"valid_original_orientation":False,"mutually_clear":False}
    D=g.labs(e[1]);A=frozenset(A);B=frozenset(B)
    a=[A&D,A-D];b=[B&D,B-D]
    HA,HB=span(g,A),span(g,B)
    clearA=[not (span(g,p)&HB) for p in a]
    clearB=[not (span(g,p)&HA) for p in b]
    nonempty=all(a+b)
    return {"valid_original_orientation":True,"edge":e,"D":D,"A_sectors":a,"B_sectors":b,"four_nonempty":nonempty,"A_sector_clear_of_HB":clearA,"B_sector_clear_of_HA":clearB,"mutually_clear":bool(nonempty and all(clearA+clearB))}


def G(raw,A,B):
    try:
        t=original(raw)
    except ValueError as exc:
        return {"G":"REFUSED","reason":str(exc)}
    all_labels=frozenset().union(*t.group.values())
    if not A or not B:
        return {"G":"REFUSED","reason":"empty_selection"}
    if any(type(x) is not int for x in list(A)+list(B)):
        return {"G":"REFUSED","reason":"noninteger_selection_label"}
    if len(A)!=len(set(A)) or len(B)!=len(set(B)):
        return {"G":"REFUSED","reason":"repeated_selection_label"}
    A=frozenset(A);B=frozenset(B)
    if not (A|B)<=all_labels:
        return {"G":"REFUSED","reason":"absent_selection_label"}
    if A&B:
        return {"G":"REFUSED","reason":"parents_not_disjoint"}
    at=addresses(t,raw);back={v:a for a,v in at.items()}
    HA,HB=span(t,A),span(t,B);shared=HA&HB
    if not shared:
        return {"G":"OUTSIDE_DISJOINT","shared_vertices":[]}
    vertices=[];degree_ok=True
    for v in sorted(shared,key=lambda v:back[v]):
        ar,br=occupied_regions(t,v,A),occupied_regions(t,v,B)
        degrees=[sum((a==v and b in h) or (b==v and a in h) for a,b in t.original_edges) for h in (HA,HB)]
        counts=[len(ar),len(br)]
        degree_ok &= counts==degrees
        vertices.append({"vertex":back[v],"graph_vertex":v,"A_regions":ar,"B_regions":br,"occupied_counts":counts,"actual_hull_degrees":degrees})
    edges=[]
    for e in t.original_edges:
        if e[0] in shared and e[1] in shared:
            z=edge_sectors(t,A,B,e)
            z["original_address_edge"]=(back[e[0]],back[e[1]])
            edges.append(z)
    edges.sort(key=lambda z:z["original_address_edge"])
    ternary=[v for v in vertices if 3 in v["occupied_counts"]]
    clear=[e for e in edges if e["mutually_clear"]]
    if not degree_ok:
        verdict="OPEN";choice={"kind":"unsupported_region_degree_correspondence"}
    elif ternary:
        verdict="FINITE-NOFIRE";choice={"kind":"three_occupied_regions","vertex":ternary[0]["vertex"]}
    elif clear:
        verdict="FINITE-NOFIRE";choice={"kind":"mutually_clear_original_edge","edge":clear[0]["original_address_edge"]}
    else:
        verdict="FIRE";choice=None
    return {"G":verdict,"choice":choice,"region_degree_correspondence":degree_ok,"shared_vertices":[v["vertex"] for v in vertices],"vertices":vertices,"shared_edges":edges,"all_shared_have_two_regions":all(v["occupied_counts"]==[2,2] for v in vertices)}


def E_guards(s,t,P,A,B,e):
    A=frozenset(A);B=frozenset(B)
    sl=frozenset().union(*s.group.values());tl=frozenset().union(*t.group.values())
    sector=edge_sectors(t,A,B,e)
    other=[frozenset(p) for p in P if frozenset(p) not in (A,B)]
    flags={"same_original_labels":sl==tl,"proper_disjoint_source_partition":partition_af(s,s,P),"selected_distinct_parent_blocks":A!=B and A in list(map(frozenset,P)) and B in list(map(frozenset,P)),"actual_oriented_original_edge":sector["valid_original_orientation"],"four_nonempty_sectors":sector.get("four_nonempty",False),"mutually_clear":sector["mutually_clear"],"outside_target_hulls_disjoint":all(not (span(t,p)&(span(t,A)|span(t,B))) for p in other),"rooted_A_homeomorphic":restriction(s,A)==restriction(t,A)}
    return {"admitted":all(flags.values()),"flags":flags,"sectors":sector}


def partitions(labels_):
    labels_=sorted(labels_)
    blocks=[]
    def rec(i):
        if i==len(labels_):
            yield pkey(blocks)
            return
        x=labels_[i]
        for b in blocks:
            b.append(x)
            yield from rec(i+1)
            b.pop()
        blocks.append([x])
        yield from rec(i+1)
        blocks.pop()
    yield from rec(0)


def bell(n):
    values=[1]
    for k in range(1,n+1):
        values.append(sum(comb(k-1,j)*values[j] for j in range(k)))
    return values[n]


def refinement_partitions(P):
    pools=[list(partitions(p)) for p in P]
    for choice in product(*pools):
        yield pkey(b for p in choice for b in p)


def outside_blocks(F,A,B):
    A=frozenset(A);B=frozenset(B)
    return pkey(b for b in F if not set(b)<=A and not set(b)<=B)


def allowed_exchange(F,Fprime,P,A,B,D):
    A=frozenset(A);B=frozenset(B);D=frozenset(D)
    return refines(Fprime,P) and tuple(sorted(A)) in Fprime and all(not set(b)<=B or set(b)<=D or not (set(b)&D) for b in Fprime) and len(Fprime)<=len(F) and outside_blocks(F,A,B)==outside_blocks(Fprime,A,B)


def construct_exchange(F,A,B,D):
    A=frozenset(A);B=frozenset(B);D=frozenset(D)
    out=[A]
    for p in F:
        p=frozenset(p)
        if p<=A:continue
        if p<=B:
            out.extend(q for q in (p&D,p-D) if q)
        else:out.append(p)
    return pkey(out)


def bounded_case(case,name,global_partition_mode=False,cap=2000,seconds=15):
    start=time.perf_counter();s,t=original(case["S"]),original(case["T"])
    P=case["P"];A=case["A"];B=case["B"]
    geometry=G(case["T"],A,B)
    labels_=frozenset().union(*s.group.values())
    denominator=bell(len(labels_)) if global_partition_mode else prod(bell(len(p)) for p in P)
    out={"case":name,"input":case,"G":geometry,"partition_mode":"all_label_partitions_then_refinement_filter" if global_partition_mode else "complete_direct_refinements_of_P","expected_candidate_denominator":denominator,"cap":cap,"time_cap_seconds":seconds}
    if frozenset().union(*t.group.values())!=labels_ or not partition_af(s,s,P):
        return {**out,"E":"REFUSED","reason":"improper_original_source_partition_or_common_labels","completed_candidates":0,"seconds":time.perf_counter()-start}
    if denominator>cap:
        return {**out,"E":"OPEN","reason":"candidate_cap_before_enumeration","completed_candidates":0,"seconds":time.perf_counter()-start}
    pool=partitions(labels_) if global_partition_mode else refinement_partitions(P)
    valid=[];seen=set();completed=0;refinement_count=0
    for F in pool:
        if time.perf_counter()-start>seconds:
            return {**out,"E":"OPEN","reason":"time_cap","completed_candidates":completed,"valid_refining_agreements_so_far":len(valid),"seconds":time.perf_counter()-start}
        completed+=1
        if F in seen:raise AssertionError("duplicate partition enumeration")
        seen.add(F)
        if not refines(F,P):continue
        refinement_count+=1
        if partition_af(t,s,F):valid.append(F)
    if completed!=denominator:
        raise AssertionError("partition denominator mismatch")
    out.update({"completed_candidates":completed,"refinement_candidates":refinement_count,"valid_refining_agreement_count":len(valid),"minimum_components_under_P":min(map(len,valid)),"minimum_components_under_P_with_A_retained":min(len(F) for F in valid if tuple(sorted(A)) in F)})
    at=addresses(t,case["T"])
    edges=[e for e in geometry.get("shared_edges",[]) if e["mutually_clear"]]
    exchanges=[];total=0;all_fires=[];construction_failures=[]
    for edge in edges:
        guard=E_guards(s,t,P,A,B,edge["edge"])
        if not guard["admitted"]:
            exchanges.append({"edge":edge["original_address_edge"],"E":"REFUSED","guards":guard})
            continue
        D=edge["D"];receipts=[]
        for F in valid:
            if time.perf_counter()-start>seconds:
                return {**out,"E":"OPEN","reason":"time_cap_in_exchanges","completed_exchange_instances":total,"seconds":time.perf_counter()-start}
            Fprime=construct_exchange(F,A,B,D)
            good=allowed_exchange(F,Fprime,P,A,B,D) and partition_af(t,s,Fprime)
            alternative=None
            if not good:
                alternative=next((Q for Q in valid if allowed_exchange(F,Q,P,A,B,D)),None)
                construction_failures.append({"edge":edge["original_address_edge"],"F":F,"constructed":Fprime,"some_other_exchange":alternative})
                if alternative is None:
                    all_fires.append({"edge":edge["original_address_edge"],"F":F,"all_eligible_exchange_candidates_exhausted":len(valid)})
            total+=1
            receipts.append({"F":F,"Fprime":Fprime if good else alternative,"construction_succeeded":good,"old_components":len(F),"new_components":len(Fprime if good else alternative) if good or alternative else None,"outside_unchanged":outside_blocks(F,A,B)==outside_blocks(Fprime,A,B) if good else None})
        exchanges.append({"edge":edge["original_address_edge"],"guards":guard,"agreement_F_denominator":len(valid),"receipts":receipts,"E":"FIRE" if any(z["edge"]==edge["original_address_edge"] for z in all_fires) else "FINITE-NOFIRE"})
    out.update({"E":"FIRE" if all_fires else "FINITE-NOFIRE" if total else "OUTSIDE_BINARY_SCOPE","exchange_instances":total,"edge_exchange_records":exchanges,"fires":all_fires,"construction_failures":construction_failures,"seconds":time.perf_counter()-start})
    return out


def substitute(raw,at,replacement):
    return replacement if type(raw) is int and raw==at else raw if type(raw) is int else [substitute(x,at,replacement) for x in raw]


def substitution_case(base,change):
    s=substitute(base["S"],change["leaf"],change["S_graft"])
    t=substitute(base["T"],change["leaf"],change["T_graft"])
    newlabels=frozenset().union(*original(change["S_graft"]).group.values())
    def expand(block):return sorted((set(block)-{change["leaf"]})|newlabels) if change["leaf"] in block else block
    return {"S":s,"T":t,"P":[expand(p) for p in base["P"]],"A":expand(base["A"]),"B":expand(base["B"])}
