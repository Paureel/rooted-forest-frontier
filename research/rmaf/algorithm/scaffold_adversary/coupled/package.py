"""Package executed records and exact integer comparisons; no experiment rerun."""
from continuation import *


def main():
    here=Path(__file__).parent
    results=here.parents[2]/"results"
    source=results/"algorithm-scaffold-adversary-coupled-pilot-v1.json"
    data=json.loads(source.read_text())
    summary=[]
    task_count=0
    for case in data["cases"]:
        rows=[]
        for selector in case["selectors"]:
            if selector["status"]!="COMPLETE":
                raise AssertionError("an OPEN consumer cannot be assigned a mass")
            vector=selector["task_vector"]
            actual_tasks=[t for e in selector["emissions"] for t in e["recursive_tasks"]]
            if vector!=[1,1]+[t["full_task_charge"] for t in actual_tasks]:
                raise AssertionError("task multiplicity mismatch")
            for task in actual_tasks:
                cost=len(set(tuple(e) for e in task["actual_source_cuts"]))
                if cost!=task["actual_source_cut_charge"]:
                    raise AssertionError("actual distinct source charge")
                if task["full_task_charge"]!=cost+task["other_parent_loss"]:
                    raise AssertionError("false extra-cut credit")
                if task["other_parent_loss"]!=sum(task["all_unresolved_ells"])-2:
                    raise AssertionError("false other-parent lower-bound charge")
                if task["query_budget"]!=task["original_budget"]-task["full_task_charge"]:
                    raise AssertionError("typed query budget mismatch")
            D=max(vector)
            num=sum(100**x*233**(D-x) for x in vector)
            den=233**D
            if str(Fraction(num,den))!=selector["task_mass"]:
                raise AssertionError("integer task mass mismatch")
            task_count+=len(actual_tasks)
            rows.append({"target_edge":selector["target_edge"],"pretest_only_vector":selector["pretest_only_vector"],"actual_task_vector":vector,"mass":selector["task_mass"],"integer_numerator":num,"integer_denominator":den,"excess_over_one_numerator":num-den,"passes":num<=den,"continuation_states":len(selector["states"]),"actual_recursive_queries":len(actual_tasks),"positive_Fitch_group_costs":[g["cost"] for state in selector["states"] for g in state["solved_good_groups"] if g["cost"]]})
        summary.append({"case":case["case"],"eligible":case["admission"]["eligible"],"selectors":rows,"passing_selectors":sum(r["passes"] for r in rows),"selector_denominator":len(rows),"seconds":case["elapsed_seconds"]})
    data["summary"]=summary
    data["recursive_query_denominator"]=task_count
    data["outcome"]="Original15 repaired at one of its two selectors; the other fixed selector still fails. Parent19 edge-selector reconstruction matches the completed development vector. No all-selector mass counterexample remains for original15 under this continuation."
    data["milestones"]={"Algorithm":"OPEN","Correctness":"OPEN","Smaller base":"OPEN"}
    data["scope"]="finite explicit continuation of the frozen independent source-core certificate; no universal algorithm, lower-bound or novelty claim; no extra independent replications"
    dest=results/"algorithm-scaffold-adversary-coupled-summary-v1.json"
    dest.write_text(json.dumps(jsonable(data),separators=(",",":"))+"\n")
    print(json.dumps({"path":str(dest),"bytes":dest.stat().st_size,"queries":task_count,"cases":summary}))


if __name__=="__main__":
    main()
