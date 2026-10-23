"""Frozen literal known-answer controls; no candidate receipts read."""
from fresh_graph import *
from pathlib import Path


def run():
    rows=[]
    def check(name, actual, expected):
        rows.append({"name":name,"actual":jsonable(actual),"expected":jsonable(expected),"pass":actual==expected})
    t3=Graph(tree(((0,1),2)))
    u3=Graph(tree(((0,2),1)))
    q=Graph(tree(((0,1),(2,3))))
    xq=Graph(tree(((0,2),(1,3))))
    # Empty assembly and singleton terminal cover empty/singleton states.
    check("empty_mass",mass([],Fraction(2)),Fraction(0))
    empty=Graph(tree(0))
    empty.remove_component(next(iter(empty.roots)))
    check("empty_forest_q",pretest(empty,empty)["q"],0)
    check("singleton_q",pretest(Graph(tree(0)),Graph(tree(0)))["q"],0)
    check("identical_q",pretest(q,q)["q"],0)
    check("incompatible_triple_zero",terminal(t3,u3)[0],False)
    check("incompatible_triple_one",pretest(t3,u3)["q"],1)
    valid=[{0,2},{1},{3}]
    invalid=[{0,2},{1,3}]
    check("crossed_valid_partition",partition_af(xq,q,valid),True)
    check("overlap_invalid_partition",partition_af(xq,q,invalid),False)
    check("overlap_invalid_reason",partition_af(xq,q,invalid,True)[1],"span_overlap")
    check("overlap_identical_terminal_invalid",partition_af(q,q,invalid),False)
    check("overlap_identical_clean_twin",partition_af(q,q,valid),True)
    overlap_forest=q.clone()
    overlap_forest.cut((0,1))
    check("actual_forest_overlap_zero",terminal(xq,overlap_forest),(False,"span_overlap"))
    check("actual_forest_overlap_one",pretest(xq,overlap_forest)["q"],1)
    colors={0:"A",1:"B",2:"A",3:"B"}
    core=colored_core(q,colors)
    extremes=[pkey([{0,2},{1},{3}]),pkey([{0},{1,3},{2}])]
    check("two_mixed_branches_cover",[any(refines(p,r["partition"]) for r in core) for p in extremes],[True,True])
    broken=colored_core(q,colors,True)
    check("missing_branch_detected",all(any(refines(p,r["partition"]) for r in broken) for p in extremes),False)
    a=colored_core(t3,{0:"A",1:"A",2:"B"})
    check("group_cut_partition",[r["partition"] for r in a],[pkey([{0,1},{2}])])
    check("group_cut_charge",[r["charge"] for r in a],[1])
    check("three_colors_charge",[r["charge"] for r in colored_core(t3,{0:"A",1:"B",2:"C"})],[2])
    b=colored_core(q,{0:"A",1:"B",2:"C",3:"A"})
    check("root_suppression_partition",[r["partition"] for r in b],[pkey([{0,3},{1},{2}])])
    check("root_suppression_charge",[r["charge"] for r in b],[2])
    check("charge_clean_twin",exact_charge([(1,2),(1,3)],2),True)
    check("false_charge_caught",exact_charge([(1,2),(1,3)],1),False)
    check("mass_clean_twin",mass([1,1],Fraction(2)),Fraction(1))
    check("false_mass_caught",mass([1,1],Fraction(2))==Fraction(3,4),False)
    # Invalid cut must fail, while the present edge's clean twin succeeds.
    clone=t3.clone()
    clone.cut(next(iter(clone.lift)))
    check("valid_edge_cut_count",len(clone.cut_history),1)
    try:
        t3.clone().cut_original((999,1000))
        rejected=False
    except ValueError:
        rejected=True
    check("invalid_edge_caught",rejected,True)
    result={"kind":"frozen_precontact_controls","rows":rows,"passed":sum(r["pass"] for r in rows),"denominator":len(rows),"all_pass":all(r["pass"] for r in rows),"core":core}
    return result


if __name__=="__main__":
    result=run()
    stamp=time.strftime("%Y%m%dT%H%M%SZ",time.gmtime())
    dest=Path(__file__).parent/f"controls-run-{stamp}.json"
    dest.write_text(json.dumps(jsonable(result),indent=2)+"\n")
    print(json.dumps({"path":str(dest),"passed":result["passed"],"denominator":result["denominator"],"all_pass":result["all_pass"]}))
    raise SystemExit(0 if result["all_pass"] else 1)
