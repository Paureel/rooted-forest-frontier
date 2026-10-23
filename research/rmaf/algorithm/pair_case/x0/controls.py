"""Constructed positive/false G/E controls, frozen before execution."""
from engine import *


def final_block_cut(s,t,P,F,B,D):
    assignment={a:i for i,b in enumerate(F) for a in b}
    realization=fitch(s,assignment)
    if realization["partition"]!=pkey(F):raise AssertionError("F source realization")
    forest=s.clone()
    for e in realization["original_cuts"]:forest.cut_original(e)
    root=next(r for r in forest.roots if forest.labs(r)==frozenset(B))
    local=component_graph(forest,root)
    cut=fitch(local,{a:int(a in D) for a in B})
    if cut["score"]!=1:raise AssertionError("agreed final B block not a one-cut rooted cluster")
    after=forest.clone()
    for e in cut["original_cuts"]:after.cut_original(e)
    if not terminal(t,after)[0]:raise AssertionError("one-cut final B-block refinement invalid")
    return {"F_source_realization":realization,"final_block":B,"actual_one_cut":cut["original_cuts"],"resulting_partition":after.partition()}


def ternary_probe(fixture):
    s,t=original(fixture["S"]),original(fixture["T"])
    A,B,P=fixture["A"],fixture["B"],fixture["P"]
    v=addresses(t,fixture["T"])[fixture["vertex"]]
    regions=occupied_regions(t,v,B)
    pool=[F for F in refinement_partitions(P) if partition_af(t,s,F)]
    def candidate(F,Q):
        return tuple(sorted(A)) in Q and all(not set(b)<=set(B) or any(set(b)<=r for r in regions) for b in Q) and len(Q)<=len(F) and outside_blocks(F,A,B)==outside_blocks(Q,A,B)
    fires=[F for F in pool if not any(candidate(F,Q) for Q in pool)]
    qualifying=[Q for Q in pool if tuple(sorted(A)) in Q and all(not set(b)<=set(B) or any(set(b)<=r for r in regions) for b in Q)]
    return {"A_regions":occupied_regions(t,v,A),"B_regions":regions,"valid_refining_agreements":len(pool),"minimum_components_under_P":min(map(len,pool)),"minimum_components_under_P_with_A_retained":min(len(F) for F in pool if tuple(sorted(A)) in F),"minimum_A_retained_and_B_regions":min(map(len,qualifying)),"fires":fires,"input_scope":"ternary diagnostic only, not licensed binary E"}


def run():
    data=json.loads((HERE/"INPUTS-v1.json").read_text());rows=[]
    def check(name,actual,expected):
        rows.append({"name":name,"actual":jsonable(actual),"expected":jsonable(expected),"pass":actual==expected})
    s=original(((1,2),3));wrong=original(((1,3),2))
    all5=list(partitions([1,2,3]));check("triple_partition_denominator",len(all5),5)
    check("identical_tree_minimum",min(len(F) for F in all5 if partition_af(s,s,F)),1)
    actual=min(len(F) for F in all5 if partition_af(s,wrong,F))
    check("wrong_rooted_topology_minimum",actual,2)
    check("false_wrong_topology_optimum_caught",actual==1,False)
    check("wrong_rooted_restriction_caught",restriction(s,{1,2,3})==restriction(wrong,{1,2,3}),False)
    q=original(((1,2),(3,4)))
    check("false_componentwise_only_forest_caught",partition_af(q,q,[[1,3],[2,4]]),False)
    check("valid_partition_clean_twin",partition_af(q,q,[[1,3],[2],[4]]),True)
    base=data["T1"];t=original(base["T"]);ss=original(base["S"]);at=addresses(t,base["T"])
    g=G(base["T"],base["A"],base["B"])
    check("T1_original_shared_vertices",g["shared_vertices"],base["expected_shared_vertices"])
    check("T1_original_region_degree_correspondence",g["region_degree_correspondence"],True)
    check("T1_clear_original_edges",[list(e["original_address_edge"]) for e in g["shared_edges"] if e["mutually_clear"]],base["expected_mutually_clear_edges"])
    e=(at["0"],at["00"])
    good=E_guards(ss,t,base["P"],base["A"],base["B"],e)
    check("T1_binary_exchange_guard_clean",good["admitted"],True)
    check("reversed_original_orientation_refused",E_guards(ss,t,base["P"],base["A"],base["B"],tuple(reversed(e)))["admitted"],False)
    check("virtual_incoming_root_edge_refused",edge_sectors(t,base["A"],base["B"],(-1,next(iter(t.roots))))["valid_original_orientation"],False)
    # A displayed A-restriction edge has two original edges, not one.
    suppressed=(at["0"],at["000"])
    check("suppressed_display_edge_is_not_original",edge_sectors(t,base["A"],base["B"],suppressed)["valid_original_orientation"],False)
    check("suppressed_original_path_length",len(path(t,leaf(1),leaf(2)))-1,4)
    check("suppressed_display_path_length",len(path(Graph(restriction(t,{1,2})),leaf(1),leaf(2)))-1,2)
    check("empty_selection_refused",G(base["T"],[],base["B"])["G"],"REFUSED")
    check("absent_selection_refused",G(base["T"],[1,999],base["B"])["G"],"REFUSED")
    check("repeated_selection_refused",G(base["T"],[1,1],base["B"])["G"],"REFUSED")
    check("repeated_original_label_refused",G(((1,1),(2,3)),[1,2],[3])["G"],"REFUSED")
    check("singleton_disjoint_outside_premise",G(base["T"],[1],base["B"])["G"],"OUTSIDE_DISJOINT")
    F=pkey(base["literal_F"]);Fp=pkey(base["literal_exchange"])
    check("literal_six_block_F_valid",partition_af(t,ss,F),True)
    check("literal_six_block_exchange_valid",partition_af(t,ss,Fp),True)
    check("literal_exchange_preserves_count",(len(F),len(Fp)),(6,6))
    check("literal_exchange_exact_construction",construct_exchange(F,base["A"],base["B"],good["sectors"]["D"]),Fp)
    check("literal_exchange_all_clauses",allowed_exchange(F,Fp,base["P"],base["A"],base["B"],good["sectors"]["D"]),True)
    source_parent_color={a:i for i,p in enumerate(base["P"]) for a in p}
    parent_real=fitch(ss,source_parent_color);parent_forest=ss.clone()
    for cut in parent_real["original_cuts"]:parent_forest.cut_original(cut)
    br=next(r for r in parent_forest.roots if parent_forest.labs(r)==frozenset(base["B"]))
    source_B=component_graph(parent_forest,br);D=good["sectors"]["D"]
    one_trials=[]
    for edge in sorted(source_B.lift):
        z=source_B.clone();z.cut(edge)
        pure=all(p<=D or not(p&D) for p in map(frozenset,z.partition()))
        one_trials.append({"actual_edge":edge,"partition":z.partition(),"two_pure_colors":pure})
    check("whole_B_one_cut_complete_trial_denominator",len(one_trials),6)
    check("false_whole_B_one_cut_claim_caught",any(x["two_pure_colors"] for x in one_trials),False)
    mincolor=fitch(source_B,{a:int(a in D) for a in base["B"]})
    check("whole_B_actual_color_split_minimum",mincolor["score"],2)
    strong=final_block_cut(ss,t,base["P"],F,[3,5],D)
    check("agreed_final_B_block_one_cut_clean_twin",len(strong["actual_one_cut"]),1)
    false3=data["false_unqualified_three_region"];u=ternary_probe(false3)
    check("unqualified_ternary_A_only_one_region",len(u["A_regions"]),1)
    check("unqualified_ternary_B_three_regions",len(u["B_regions"]),3)
    check("unqualified_ternary_literal_F_valid",partition_af(original(false3["T"]),original(false3["S"]),false3["F"]),True)
    check("unqualified_ternary_minimum_forced_completion",u["minimum_A_retained_and_B_regions"],4)
    check("false_unqualified_ternary_exchange_caught",pkey(false3["F"]) in u["fires"],True)
    return {"scope":"frozen controls before bounded G/E attack, same old checker lineage","rows":rows,"passed":sum(r["pass"] for r in rows),"denominator":len(rows),"all_pass":all(r["pass"] for r in rows),"T1_geometry":g,"whole_B_one_cut_refusals":one_trials,"whole_B_two_cut_witness":mincolor,"final_B_block_actual_one_cut_witness":strong,"false_unqualified_ternary":u}


if __name__=="__main__":
    result=run();stamp=time.strftime("%Y%m%dT%H%M%SZ",time.gmtime());out=HERE/f"controls-{stamp}.json";save(out,result)
    print(json.dumps({"path":str(out),"passed":result["passed"],"denominator":result["denominator"],"all_pass":result["all_pass"],"failures":[r["name"] for r in result["rows"] if not r["pass"]]}))
    raise SystemExit(0 if result["all_pass"] else 1)
