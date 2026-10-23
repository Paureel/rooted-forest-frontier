"""Additional admission/core plants before any pair14 contact; no old edits."""
from controls import *


def run_supplement():
    rows=[]
    def check(name,value,expected):
        rows.append({"name":name,"actual":jsonable(value),"expected":jsonable(expected),"pass":value==expected})
    fixture=json.loads((HERE/"CONTROL-INPUTS.json").read_text())
    base=fixture["base10"]
    clean=evaluate(base["T"],base["Tprime"],base["selected"],False)
    check("source_rule67_clean_twin",clean["rules67"]["excluded"],True)
    t6=Graph(tree((((0,2),1),((3,4),(5,6)))))
    s6=make_components((((0,1),((2,3),4)),(5,6)),[{0,1},{2,3,4},{5,6}])
    r6=rules67(t6,s6,classification(t6,s6))
    check("source_rule6_one_edge_false_admission_caught",r6["excluded"],False)
    check("source_rule6_actual_single_edge",len(r6["rule6"]),1)
    t7=Graph(tree((((0,1),(2,3)),(4,5))))
    s7=make_components((((0,2),(1,3)),(4,5)),[{0,2},{1,3},{4,5}])
    r7=rules67(t7,s7,classification(t7,s7))
    check("source_rule7_closed_good_overlap_false_admission_caught",r7["excluded"],False)
    q=Graph(tree(((0,1),(2,3))))
    colors={0:"A",1:"B",2:"A",3:"B"}
    extremes=[pkey([{0,2},{1},{3}]),pkey([{0},{1,3},{2}])]
    complete=colored_core(q,colors)
    incomplete=colored_core(q,colors,omit_second=True)
    def covers(core):
        return all(any(refines(p,row["partition"]) for row in core) for p in extremes)
    check("source_core_two_branches_clean_coverage",covers(complete),True)
    check("source_core_missing_branch_caught",covers(incomplete),False)
    tq=Graph(tree(((0,1),(2,3))))
    sq=make_components(((0,2),(1,3)),[{0,2},{1,3}])
    completed=good_completion(tq,sq,[0,1],classification(tq,sq))
    check("Fitch_source_witness_charge_clean",exact_charge(completed["additional_source_cuts"],completed["cost"]),True)
    check("Fitch_source_witness_missing_actual_cut_caught",exact_charge([],completed["cost"]),False)
    return {"scope":"supplementary pre-release source67/core-consumer plants, same existing checker lineage; no pair14 contact","rows":rows,"passed":sum(r["pass"] for r in rows),"denominator":len(rows),"all_pass":all(r["pass"] for r in rows)}


if __name__=="__main__":
    result=run_supplement()
    stamp=time.strftime("%Y%m%dT%H%M%SZ",time.gmtime())
    path=HERE/f"supplementary-controls-{stamp}.json"
    save(path,result)
    print(json.dumps({"path":str(path),"passed":result["passed"],"denominator":result["denominator"],"all_pass":result["all_pass"]}))
    raise SystemExit(0 if result["all_pass"] else 1)
