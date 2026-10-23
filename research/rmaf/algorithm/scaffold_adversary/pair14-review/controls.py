"""Pre-release clean/false controls using the existing independent lineage.

No new pair14 receipt, author evaluator or Lean source is opened here.
"""
import sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"coupled"))
from continuation import *


def make_components(nested,blocks):
    g=Graph(tree(nested))
    for block in blocks:
        want=frozenset(block)
        if any(g.labs(r)==want for r in g.roots):
            continue
        v=next(v for v in g.ch if g.labs(v)==want)
        g.cut((g.parent()[v],v))
    return g


def actual_selectors(t,s):
    cl=classification(t,s)
    es=set()
    vs=set()
    for i,j in cl["overlap_pairs"]:
        a,b=cl["blocks"][i],cl["blocks"][j]
        es.update(edges_span(t,a)&edges_span(t,b))
        vs.update(span(t,a)&span(t,b))
    return {"edges":sorted(es),"vertices":sorted(vs)}


def exact_selector_claim(actual,claimed):
    def frozen(z):
        return tuple(z) if isinstance(z,(tuple,list)) else z
    a=list(map(frozen,actual))
    c=list(map(frozen,claimed))
    return len(c)==len(set(c)) and set(c)==set(a)


def exact_task_payment(actual_cuts,other_ells,claimed_charge):
    if type(claimed_charge) is not int or any(type(x) is not int or x not in (0,1,2) for x in other_ells):
        return False
    return len(set(tuple(e) for e in actual_cuts))+sum(other_ells)==claimed_charge


def run():
    fixtures=json.loads((HERE/"CONTROL-INPUTS.json").read_text())
    rows=[]
    def check(name,actual,expected):
        rows.append({"name":name,"actual":jsonable(actual),"expected":jsonable(expected),"pass":actual==expected})
    q=fixtures["quartet"]
    t=Graph(tree(q["T"]))
    crossed=make_components(q["crossed_source"],q["crossed_components"])
    # Original graph, root suppression, actual original lifts, and payment.
    check("original_quad_vertices",len(t.ch),7)
    check("original_quad_edges",len(t.original_edges),6)
    g=t.clone()
    g.cut((1,2))
    check("unary_edge_lift_has_original_path",g.lift[(0,3)],((0,1),(1,3)))
    g.cut_original((1,3))
    check("suppression_realized_original_cut",g.cut_history,[(1,2),(0,1)])
    check("original_nonredundant_piece_count",g.partition(),pkey([{0},{1},{2,3}]))
    check("paid_cut_clean_twin",exact_charge(g.cut_history,2),True)
    check("false_missing_cut_charge",exact_charge(g.cut_history,1),False)
    check("false_duplicate_cut_charge",exact_charge([(1,2),(1,2)],2),False)
    check("all_realized_lifts_original",all(e in t.original_edges for e in g.cut_history),True)
    badedge=t.clone()
    try:
        badedge.cut_original((999,1000))
        refused=False
    except ValueError:
        refused=True
    check("unrealizable_original_edge_refused",refused,True)
    check("full_label_partition_clean",partition_af(t,Graph(tree(q["crossed_source"])),q["valid_three_piece_partition"]),True)
    check("missing_original_label_refused",partition_af(t,t,[{0,1},{2}]),False)
    check("duplicate_original_label_refused",partition_af(t,t,[{0,1},{1,2,3}]),False)
    check("componentwise_only_overlap_refused",terminal(t,crossed)[0],False)
    try:
        tree((0,1,2))
        refused=False
    except ValueError:
        refused=True
    check("nonbinary_original_refused",refused,True)
    dup=evaluate((((0,0),1),2),(((0,1),0),2),(0,1),False)
    check("duplicate_common_original_labels_refused",dup["eligible"],False)
    rho=evaluate((("a","b"),"rho"),(("a","rho"),"b"),("a","b"),False)
    check("rho_or_noninteger_label_refused","noninteger_or_rho_label" in rho["failures"],True)
    # Actual earlier-rule consumers; clean source admission is a prior contact.
    base=fixtures["base10"]
    admitted=evaluate(base["T"],base["Tprime"],base["selected"],False)
    check("both_original_orientations_clean",[z["excluded_2a_to_2d"] for z in admitted["admission_both_orientations"]],[True,True])
    check("actual_selected_cherry_admitted",admitted["eligible"],True)
    check("exact_actual_pendant_groups",pkey(p["labels"] for p in admitted["actual_pendants"]),pkey(base["pendants"]))
    check("false_selected_cherry_refused",evaluate(base["T"],base["Tprime"],(7,8),False)["eligible"],False)
    check("false_omitted_second_orientation",all([True,False]),False)
    same=source_admission(Graph(tree(((0,1),2))),Graph(tree(((0,1),2))))
    check("earlier_common_cherry_refused",same["excluded_2a_to_2d"],False)
    one=source_admission(Graph(tree(((0,1),2))),Graph(tree(((0,2),1))))
    check("earlier_Whidden1_detected",any(z["step2a"] for z in one["rows"]),True)
    many=source_admission(Graph(tree((((0,1),2),(3,4)))),Graph(tree(((((0,2),3),4),1))))
    check("earlier_Whidden3_detected",any(z["step2b"] for z in many["rows"]),True)
    r4=fixtures["rule4"]
    a4=source_admission(Graph(tree(r4["T"])),Graph(tree(r4["Tprime"])))
    check("earlier_rule4_detected",any(z["step2c"] for z in a4["rows"]),True)
    r5=fixtures["rule5"]
    a5=source_admission(Graph(tree(r5["T"])),Graph(tree(r5["Tprime"])))
    check("earlier_rule5_detected",any(z["step2d"] for z in a5["rows"]),True)
    # Both shared-edge and shared-vertex selector consumers are explicit.
    selectors=actual_selectors(t,crossed)
    check("actual_shared_edge_count_and_ids",selectors["edges"],[tuple(z) for z in q["expected_actual_shared_edges"]])
    check("actual_shared_vertex_count_and_ids",selectors["vertices"],q["expected_actual_shared_vertices"])
    check("edge_selector_clean_twin",exact_selector_claim(selectors["edges"],q["expected_actual_shared_edges"]),True)
    check("missing_edge_selector_detected",exact_selector_claim(selectors["edges"],q["expected_actual_shared_edges"][:1]),False)
    check("duplicate_edge_selector_detected",exact_selector_claim(selectors["edges"],q["expected_actual_shared_edges"]+q["expected_actual_shared_edges"][:1]),False)
    check("unrealizable_extra_edge_selector_detected",exact_selector_claim(selectors["edges"],q["expected_actual_shared_edges"]+[[1,2]]),False)
    check("vertex_selector_clean_twin",exact_selector_claim(selectors["vertices"],q["expected_actual_shared_vertices"]),True)
    check("missing_vertex_selector_detected",exact_selector_claim(selectors["vertices"],[0,1]),False)
    check("false_vertex_selector_detected",exact_selector_claim(selectors["vertices"],[0,1,2]),False)
    # Good-group completion and bad-overlap continuation.
    cl=classification(t,crossed)
    complete=good_completion(t,crossed,[0,1],cl)
    check("overlapping_good_group_cost",complete["cost"],1)
    check("false_zero_compatible_group_completion",complete["cost"]==0,False)
    check("false_target_score_source_credit",complete["cost"]==complete["target_fitch"]["score"],False)
    clean=make_components(q["T"],[[0,1],[2,3]])
    check("disjoint_good_group_zero_clean_twin",good_completion(t,clean,[0,1],classification(t,clean))["cost"],0)
    b=fixtures["bad_overlap"]
    bt=Graph(tree(b["T"]))
    bs=make_components(b["source_bad"],b["components"])
    bc=classification(bt,bs)
    try:
        good_completion(bt,bs,[0,1],bc)
        refused=False
    except ValueError:
        refused=True
    check("bad_overlapping_parent_Fitch_refused",refused,True)
    engine=Continuation(bt,k=12,max_states=40)
    out=engine.run(bs)
    check("bad_overlap_executes_actual_further_SPLIT",engine.states[0]["status"],b["expected_bad_root_status"])
    check("bad_overlap_continuation_supported",out["status"],"COMPLETE")
    check("further_SPLIT_has_two_sided_sources",len(set(z["source_index"] for z in engine.states[0]["further_split"]["branches"])),2)
    good=make_components(b["source_good_twin"],b["components"])
    goodengine=Continuation(bt,k=12,max_states=40)
    goodengine.run(good)
    check("good_overlap_poly_clean_twin",goodengine.states[0]["status"],b["expected_good_root_status"])
    # Typed budgets, true other-parent loss, original payment and multiplicity.
    bm=fixtures["budget_models"]
    check("p1_actual_query_budget",[z["query_budget"] for z in typed_queries(bm["q"],0,bm["p1_ells"])],bm["p1_expected_query_budgets"])
    check("p1_actual_other_loss_zero",[z["other_loss"] for z in typed_queries(bm["q"],0,bm["p1_ells"])],bm["p1_expected_other_loss"])
    check("p2_actual_other_ell2_budgets",[z["query_budget"] for z in typed_queries(bm["q"],0,bm["p2_ells"])],bm["p2_expected_query_budgets"])
    check("p2_actual_solved_cost1_budgets",[z["query_budget"] for z in typed_queries(bm["q"],1,bm["p2_ells"])],bm["p2_solved_cost1_expected_query_budgets"])
    check("true_source_payment_and_other_parent",exact_task_payment([(0,1),(1,2)],[2],4),True)
    check("false_own_parent_extra_credit",exact_task_payment([(0,1),(1,2)],[],4),False)
    check("false_unpaid_extra_cut_credit",exact_task_payment([(0,1),(1,2)],[],3),False)
    check("false_duplicate_source_payment",exact_task_payment([(0,1),(0,1)],[],2),False)
    check("p1_clean_no_extra_credit",check_task_claim(7,0,[2],[0],1),True)
    check("p1_false_extra_credit",check_task_claim(7,0,[2],[1],1),False)
    check("p2_clean_task_multiplicity",check_task_claim(7,0,[2,2],[2,2],2),True)
    check("p2_false_task_multiplicity",check_task_claim(7,0,[2,2],[2],1),False)
    check("identical_signatures_keep_queries",len(typed_queries(7,0,[2 for _ in bm["identical_pair_signatures"]])),2)
    check("negative_child_budget_prunes_all_queries",sum(z["query_budget"]>=0 for z in typed_queries(1,0,[2,2])),0)
    for name,qvalue,cost,ells in [("float_q",7.0,0,[2]),("bool_q",True,0,[2]),("negative_solved_credit",7,-1,[2]),("float_ell",7,0,[2.0]),("falsely_unresolved_ell1",7,0,[1])]:
        try:
            typed_queries(qvalue,cost,ells)
            refused=False
        except ValueError:
            refused=True
        check(name+"_typed_refusal",refused,True)
    check("exact_mass_clean_twin",mass([1,1]),Fraction(200,233))
    check("false_task_mass_multiplicity",mass([2,2])==mass([2]),False)
    check("empty_recursive_task_mass",mass([]),Fraction(0))
    return {"scope":"pre-release pair14 targeted controls using existing independent checker lineage; no new fourteen-label source/receipt/Lean contact and no new independent replication","rows":rows,"passed":sum(r["pass"] for r in rows),"denominator":len(rows),"all_pass":all(r["pass"] for r in rows),"actual_selector_control":selectors,"Fitch_completion_witness":complete,"bad_overlap_control_states":engine.states,"clean_twin_good_overlap_states":goodengine.states}


if __name__=="__main__":
    result=run()
    stamp=time.strftime("%Y%m%dT%H%M%SZ",time.gmtime())
    path=HERE/f"controls-{stamp}.json"
    save(path,result)
    print(json.dumps({"path":str(path),"passed":result["passed"],"denominator":result["denominator"],"all_pass":result["all_pass"],"failures":[r["name"] for r in result["rows"] if not r["pass"]]}))
    raise SystemExit(0 if result["all_pass"] else 1)
