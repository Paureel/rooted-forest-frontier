"""Postcontact original-source guards and internal hard-pair exact witness.

These controls are weaker than the frozen precontact controls; explicitly scoped.
"""
from scaffold import *


def make_forest(t,blocks):
    g=Graph(tree(t))
    for block in blocks:
        b=frozenset(block)
        if any(g.labs(r)==b for r in g.roots):
            continue
        v=next(v for v in g.ch if g.labs(v)==b)
        p=g.parent()[v]
        g.cut((p,v))
    return g


def main():
    rows=[]
    def check(name,actual,expected):
        rows.append({"name":name,"actual":jsonable(actual),"expected":jsonable(expected),"pass":actual==expected})
    fixtures=json.loads((Path(__file__).parent/"literal-inputs.json").read_text())
    base=fixtures["base"]
    clean=evaluate(base["T"],base["Tprime"],include_boundaries=False)
    check("original_source_clean_twin",clean["eligible"],True)
    check("bad_selected_cherry",evaluate(base["T"],base["Tprime"],(7,8),False)["eligible"],False)
    same=source_admission(Graph(tree(((0,1),2))),Graph(tree(((0,1),2))))
    check("common_cherry_refusal",same["excluded_2a_to_2d"],False)
    t1=source_admission(Graph(tree(((0,1),2))),Graph(tree(((0,2),1))))
    check("Whidden_t1_caught",any(r["step2a"] for r in t1["rows"]),True)
    t3=source_admission(Graph(tree((((0,1),2),(3,4)))),Graph(tree(((((0,2),3),4),1))))
    check("Whidden_t3_caught",any(r["step2b"] for r in t3["rows"]),True)
    r4=source_admission(Graph(tree((((((4,5),3),2),1),0))),Graph(tree(((((1,3),4),(2,5)),0))))
    check("rule4_caught",any(r["step2c"] for r in r4["rows"]),True)
    r5=source_admission(Graph(tree(((0,1),((2,3),4)))),Graph(tree((((0,(2,3)),4),1))))
    check("rule5_caught",any(r["step2d"] for r in r5["rows"]),True)
    tr6=Graph(tree((((0,2),1),((3,4),(5,6)))))
    sr6=make_forest((((0,1),((2,3),4)),(5,6)),[{0,1},{2,3,4},{5,6}])
    cl6=classification(tr6,sr6)
    check("rule6_single_edge_caught",len(rules67(tr6,sr6,cl6)["rule6"]),1)
    tr7=Graph(tree((((0,1),(2,3)),(4,5))))
    sr7=make_forest((((0,2),(1,3)),(4,5)),[{0,2},{1,3},{4,5}])
    r7=rules67(tr7,sr7,classification(tr7,sr7))
    check("rule7_closed_homeomorphic_overlap_caught",r7["excluded"],False)
    check("rule67_clean_twin",clean["rules67"]["excluded"],True)
    hard=fixtures["hard"]
    ht,hs=Graph(tree(hard["T"])),Graph(tree(hard["Tprime"]))
    depth=pretest(ht,hs)
    check("hard_pair_zero_one_refused",depth["solved"],False)
    witness=None
    tested=0
    invalid=0
    for cuts in combinations(hs.original_edges,2):
        z=hs.clone()
        try:
            for e in cuts:
                z.cut_original(e)
        except ValueError:
            invalid+=1
            continue
        tested+=1
        if terminal(ht,z)[0]:
            witness={"cuts":cuts,"actual_cuts":z.cut_history,"partition":z.partition()}
            break
    check("hard_pair_two_cut_witness",witness is not None,True)
    result={"scope":"postcontact original-source controls; all expected outcomes authored before this control run","rows":rows,"passed":sum(r["pass"] for r in rows),"denominator":len(rows),"hard_pair_exact_minimum_cuts":2 if not depth["solved"] and witness else None,"hard_pair_pretest":depth,"hard_pair_two_cut_witness":witness,"two_cut_trials_to_witness":tested,"suppressed_redundant_combinations":invalid}
    save(Path(__file__).parent/"source-controls-v1.json",result)
    print(json.dumps({"passed":result["passed"],"denominator":len(rows),"hard_pair_minimum":result["hard_pair_exact_minimum_cuts"],"failed":[r["name"] for r in rows if not r["pass"]]}))
    raise SystemExit(0 if all(r["pass"] for r in rows) else 1)


if __name__=="__main__":
    main()
