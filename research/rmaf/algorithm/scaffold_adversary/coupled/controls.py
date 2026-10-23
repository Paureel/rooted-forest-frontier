"""New positive/false controls frozen before coupled execution."""
from continuation import *


def two_component_source(pair1,pair2):
    g=Graph(tree((pair1,pair2)))
    first=frozenset(pair1)
    v=next(v for v in g.ch if g.labs(v)==first)
    g.cut((g.parent()[v],v))
    return g


def exact_good_group_oracle(t,s,maxcuts=1):
    """TEST ONLY: bounded explicit cut enumeration on a tiny group."""
    for q in range(maxcuts+1):
        for cuts in combinations(tuple(sorted(s.lift)),q):
            z=s.clone()
            try:
                for e in cuts:
                    z.cut_original(min(s.lift[e]))
            except ValueError:
                continue
            if terminal(t,z)[0]:
                return q
    return None


def run():
    rows=[]
    def check(name,value,expected):
        rows.append({"name":name,"actual":jsonable(value),"expected":jsonable(expected),"pass":value==expected})
    t=Graph(tree(((0,1),(2,3))))
    overlapping=two_component_source((0,2),(1,3))
    cl=classification(t,overlapping)
    check("overlap_pair_individual_matches",cl["homeomorphic"],[True,True])
    check("overlap_not_terminal",terminal(t,overlapping)[0],False)
    completion=good_completion(t,overlapping,[0,1],cl)
    check("Fitch_target_score",completion["target_fitch"]["score"],2)
    check("Fitch_additional_source_cuts",completion["cost"],1)
    check("Fitch_true_source_cut_count",len(completion["additional_source_cuts"]),1)
    check("quartet_test_oracle",exact_good_group_oracle(t,overlapping),1)
    check("false_zero_completion_caught",completion["cost"]==0,False)
    clean=two_component_source((0,1),(2,3))
    zero=good_completion(t,clean,[0,1],classification(t,clean))
    check("Fitch_disjoint_zero_clean_twin",zero["cost"],0)
    check("zero_twin_test_oracle",exact_good_group_oracle(t,clean),0)
    check("false_target_score_as_source_charge_caught",completion["cost"]==completion["target_fitch"]["score"],False)
    check("p1_other_loss_zero",typed_queries(7,0,[2]),[{"index":0,"other_loss":0,"solved_cost":0,"query_budget":7,"task_additional_charge":0}])
    check("p2_actual_other_ell2_budgets",[z["query_budget"] for z in typed_queries(7,0,[2,2])],[5,5])
    check("p2_solved_cut1_budgets",[z["query_budget"] for z in typed_queries(7,1,[2,2])],[4,4])
    check("p1_clean_zero_extra_credit",check_task_claim(7,0,[2],[0],1),True)
    check("p1_false_extra_cut_credit",check_task_claim(7,0,[2],[1],1),False)
    check("p2_clean_task_multiplicity",check_task_claim(7,0,[2,2],[2,2],2),True)
    check("p2_false_task_multiplicity",check_task_claim(7,0,[2,2],[2],1),False)
    signatures=["same","same"]
    check("identical_pairs_keep_two_tasks",len(typed_queries(7,0,[2 for _ in signatures])),2)
    check("exact_task_mass",mass([2,2]),Fraction(20000,54289))
    check("false_single_task_mass",mass([2,2])==mass([2]),False)
    check("empty_task_mass",mass([]),Fraction(0))
    for name,q,cost,ells in [("float_q",7.0,0,[2]),("bool_q",True,0,[2]),("negative_credit",7,-1,[2]),("false_ell1_unresolved",7,0,[1]),("float_ell",7,0,[2.0])]:
        try:
            typed_queries(q,cost,ells)
            refused=False
        except ValueError:
            refused=True
        check("typed_"+name+"_refused",refused,True)
    badt=Graph(tree(((0,1),2)))
    bads=Graph(tree(((0,2),1)))
    badcl=classification(badt,bads)
    try:
        good_completion(badt,bads,[0],badcl)
        refused=False
    except ValueError:
        refused=True
    check("bad_parent_Fitch_refused",refused,True)
    return {"scope":"new coupled controls, expected outputs pinned before execution; exact enumeration is test-only","rows":rows,"passed":sum(r["pass"] for r in rows),"denominator":len(rows),"fitch_positive_witness":completion,"fitch_zero_twin":zero,"all_pass":all(r["pass"] for r in rows)}


if __name__=="__main__":
    result=run()
    stamp=time.strftime("%Y%m%dT%H%M%SZ",time.gmtime())
    path=Path(__file__).parent/f"controls-{stamp}.json"
    save(path,result)
    print(json.dumps({"path":str(path),"passed":result["passed"],"denominator":result["denominator"],"all_pass":result["all_pass"]}))
    raise SystemExit(0 if result["all_pass"] else 1)
