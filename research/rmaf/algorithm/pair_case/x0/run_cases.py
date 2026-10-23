"""Measured tiny pilot, then separately launched bounded frozen hostile cases."""
from controls import *
import argparse


def main():
    parser=argparse.ArgumentParser();parser.add_argument("mode",choices=["pilot","hostile"]);args=parser.parse_args()
    data=json.loads((HERE/"INPUTS-v1.json").read_text());results=HERE.parents[2]/"results"
    cases=[]
    if args.mode=="pilot":
        for name in ["T1","root_promoted6"]:
            row=bounded_case(data[name],name,True)
            if row["E"] in ("OPEN","FIRE"):pass
            else:
                expected=data[name]
                assert row["completed_candidates"]==expected["expected_global_partition_generation_count"]
                assert row["minimum_components_under_P"]==expected["expected_refinement_constrained_min_components"]
                assert row["minimum_components_under_P_with_A_retained"]==expected["expected_refinement_constrained_A_retained_min_components"]
            cases.append(row)
            save(HERE/f"{args.mode}-progress.json",{"cases":cases})
            print(json.dumps({k:row.get(k) for k in ["case","E","completed_candidates","refinement_candidates","valid_refining_agreement_count","minimum_components_under_P","minimum_components_under_P_with_A_retained","exchange_instances","seconds"]}),flush=True)
    else:
        for sub in data["hostile_substitutions"]:
            fixture=substitution_case(data["T1"],sub)
            row=bounded_case(fixture,sub["name"])
            cases.append(row);save(HERE/f"{args.mode}-progress.json",{"cases":cases})
            print(json.dumps({k:row.get(k) for k in ["case","E","completed_candidates","refinement_candidates","valid_refining_agreement_count","minimum_components_under_P","minimum_components_under_P_with_A_retained","exchange_instances","seconds"]}),flush=True)
        three=data["genuine_three_region_probe"]
        row=bounded_case(three,"genuine_three_region_probe")
        diagnostic=ternary_probe(three)
        assert row["minimum_components_under_P"]==three["expected_refinement_constrained_min_components"]
        assert row["minimum_components_under_P_with_A_retained"]==three["expected_refinement_constrained_A_retained_min_components"]
        row["unlicensed_ternary_diagnostic"]=diagnostic
        cases.append(row)
        print(json.dumps({"case":row["case"],"G":row["G"]["G"],"G_choice":row["G"]["choice"],"E":row["E"],"ternary_fires":len(diagnostic["fires"]),"seconds":row["seconds"]}),flush=True)
    output={"mode":args.mode,"scope":"bounded original-graph X0 only; same checker lineage; finite no-fire proves no universal G/E theorem","cases":cases,"milestones":{"Algorithm":"OPEN","Correctness":"OPEN","Smaller base":"OPEN"}}
    path=results/f"algorithm-pair-case-x0-{args.mode}-v1.json";save(path,output)
    print(json.dumps({"result":str(path),"completed_cases":len(cases)}),flush=True)


if __name__=="__main__":main()
