"""Bounded coupled pilot on the original15leaf and single parent19leaf contact."""
from continuation import *


def main():
    here=Path(__file__).parent
    results=here.parents[2]/"results"
    own=json.loads((results/"algorithm-scaffold-adversary-H2-witness-v1.json").read_text())
    contact_path=results/"algorithm-universal233-scaffold-hard-plant-summary-v1.json"
    contact=json.loads(contact_path.read_text())
    data=[("original15",own["original"]["T"],own["original"]["Tprime"],own["selected_cherry"]),("parent19_contact",contact["original_T"],contact["original_Tprime"],contact["selected_cherry"])]
    result={"kind":"bounded coupled pilot; no extra independent replication","new_contact":{"path":str(contact_path),"sha256":hashlib.sha256(contact_path.read_bytes()).hexdigest(),"status":"development data contact; reconstructed independently from original graphs before reported vector comparison"},"initial_budget":12,"state_cap_per_selector":200,"cases":[]}
    for name,t,s,selected in data:
        start=time.perf_counter()
        # Eligibility is recomputed by the same preexisting independent checker lineage.
        admission=evaluate(t,s,selected,include_boundaries=False)
        if not admission["eligible"]:
            raise AssertionError(("continued literal out of source regime",name,admission))
        rows=initial_selectors(t,s,selected,k=12)
        item={"case":name,"original_T":t,"original_Tprime":s,"selected_cherry":selected,"admission":admission,"selectors":rows,"elapsed_seconds":time.perf_counter()-start}
        if name=="parent19_contact":
            expected=sorted(contact["rows"][0]["actual_paid_recursive_task_vector"])
            item["reported_contact_vector"]=expected
            item["reported_contact_mass"]=contact["rows"][0]["actual_paid_mass"]
            item["reconstructed_comparison"]=[{"edge":r["target_edge"],"vector_matches":sorted(r["task_vector"])==expected if r["task_vector"] is not None else None,"mass_matches":str(r["task_mass"])==item["reported_contact_mass"]} for r in rows]
        result["cases"].append(item)
        save(here/"pilot-progress.json",result)
        print(json.dumps({"case":name,"seconds":item["elapsed_seconds"],"eligible":True,"selectors":[{"edge":r["target_edge"],"raw":r["raw_vector"],"pretest":r["pretest_only_vector"],"tasks":r["task_vector"],"mass":str(r["task_mass"]),"status":r["status"],"states":len(r["states"])} for r in rows]}),flush=True)
    result["completed_cases"]=len(result["cases"])
    save(results/"algorithm-scaffold-adversary-coupled-pilot-v1.json",result)


if __name__=="__main__":
    main()
