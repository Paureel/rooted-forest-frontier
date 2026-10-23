"""One-shot local independent Rule4 source seal; no global acceptance implied."""
import datetime,hashlib,json,pathlib,re
H=pathlib.Path(__file__).resolve().parent;PRE=H.parent
ROOT=next(p for p in H.parents if(p/"bootloops-python").exists())
def sha(p):
    d=hashlib.sha256()
    with p.open("rb")as f:
        while b:=f.read(1024*1024):d.update(b)
    return d.hexdigest()
def put(name,obj):(H/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+"\n")
def get(name):return json.loads((H/name).read_text())
def main():
    for n in["SOURCE-REVIEW-SEAL-v1.json","SOURCE-REVIEW-MANIFEST-v1.json","QUALITY-CHECKS-v1.json"]:
        if(H/n).exists():raise RuntimeError("seal already exists "+n)
    release=ROOT/"research/rmaf/algorithm/verification/rule4-2026-10-15/ROOT-RELEASE-v1.json";rel=json.loads(release.read_text())
    assert sha(PRE/"READY-v1.json")==rel["READY_sha256"]
    prem=json.loads((PRE/"PRERELEASE-MANIFEST-v1.json").read_text())
    assert sha(PRE/"PRERELEASE-MANIFEST-v1.json")==rel["readiness_manifest_sha256"]
    for r in prem["files"]:
        p=PRE/r["path"];assert sha(p)==r["sha256"]and not(p.stat().st_mode&0o222)
    author=ROOT/rel["author_manifest"];assert sha(author)==rel["author_manifest_sha256"]
    am=json.loads(author.read_text());ap=am["immutable_files"]+am["external_input_pins"]
    for r in ap:assert sha(ROOT/r["path"])==r["sha256"]and(ROOT/r["path"]).stat().st_size==r["bytes"]
    dag=get("source-dag.json");assert dag["count"]==95 and dag["copied_scientific_oleans"]==0
    builds=[json.loads(s)for s in(H/"build-execution.jsonl").read_text().splitlines()]
    assert len(builds)==95 and all(r["returncode"]==0 for r in builds)
    assert {r["module"]for r in builds}==set(dag["order"])
    for n,row in dag["sources"].items():assert sha(H/"cold-source"/(n+".lean"))==row["sha256"]
    provenance=get("producer-validation-all.json")
    assert provenance["complete"]and provenance["producers"]==95 and provenance["stored_occurrences"]==3513 and provenance["unique_names"]==3487
    assert provenance["axiom_union"]==["Classical.choice","Quot.sound","propext"]and not provenance["uninspected_extra_ConstantInfos"]
    lean=get("lean-runtime-all-v2-validation.json");assert lean["passed"]==288 and lean["actual_callback_traces"]==90 and len(lean["mutations"])==7
    python=get("runtime-python-all-v2.json");assert python["passed"]==252 and len(python["fixtures"])==5
    false=get("false-source-execution-v2.json");assert false["returncode"]==1 and len(false["error_headers"])==5
    assert false["stdout"].count("Tactic `decide` proved that the proposition")==5 and false["stdout"].count("is false")==5
    guard=get("guard-readout-validation-v3.json");assert guard["passed_guard_cases"]==6
    domain=json.loads((H/"domain-readout.stdout").read_text())
    expected={"target_Q_embeddings":False,"source_Q_embeddings":True,"proper":True,"state_agrees":True,
      "missing_source_agrees":False,"absent_raw_guard":False,"root_cut_partition":False,
      "root_cut_filtered_state_proper":True,"duplicate_cut_partition":False,"absent_cut_partition":False,"comparable_cut_partition":False}
    assert domain==expected
    render=get("report-render-receipt.json");assert len(render)==4 and all(r["tables"]==1 for r in render)
    for name in["FINAL-REVIEW.md","SOURCE-WORK.md","CONSUMER-TRACE.md"]:
        text=(H/name).read_text()
        assert not re.search(r"delve|tapestry|leverage|unlock|seamless|cutting.edge|groundbreaking",text,re.I)
    # All counters carry units; never sum overlapping pilot/full readout counts.
    quality={"pre_READY_members_unchanged":len(prem["files"]),"author_pins_unchanged":len(ap),
      "cold_positive_source_modules":len(builds),"stored_producer_occurrences":provenance["stored_occurrences"],
      "resolved_scientific_names":provenance["unique_names"],"python_fixed_checks":python["passed"],
      "Lean_fixed_checks":lean["passed"],"actual_callback_traces":lean["actual_callback_traces"],
      "caught_runtime_comparator_mutations":len(lean["mutations"]),"actual_guard_classes":guard["passed_guard_cases"],
      "released_false_propositions_rejected":5,"rendered_reports":len(render),
      "local_prose_passes":"meaning/number/locator pass; rendered-text/table and colleague pass; changes retained",
      "pixel_visual_inspection":False,"fresh_context_framing":"PENDING_SEPARATE_ROOT_REVIEW","all_main_milestones":"OPEN"}
    put("QUALITY-CHECKS-v1.json",quality)
    files=[]
    for p in sorted(H.rglob("*")):
        if not p.is_file()or"__pycache__"in p.parts or p.suffix==".pyc":continue
        files.append({"path":str(p.relative_to(H)),"bytes":p.stat().st_size,"sha256":sha(p)})
    manifest={"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"files":files,"excluded":"runtime __pycache__/*.pyc only"}
    put("SOURCE-REVIEW-MANIFEST-v1.json",manifest)
    metas=[json.loads(p.read_text())for p in(H/"producer-audits").glob("*.meta.json")]
    seal={"status":"INDEPENDENT_LOCAL_RULE4_SOURCE_REVIEW_SEALED","root_release_sha256":sha(release),
      "READY_sha256":rel["READY_sha256"],"author_manifest_sha256":rel["author_manifest_sha256"],
      "source_review_manifest_sha256":sha(H/"SOURCE-REVIEW-MANIFEST-v1.json"),"source_review_members":len(files),
      "semantic":"CONFIRMED_LOCAL_ORIGINAL_RULE4_COVER","interface":"CONFIRMED_CONDITIONAL_ON_LITERAL_EXACT_CHILD",
      "provenance":"CONFIRMED_STORED_PRODUCER_STANDARD_AXIOMS_ONLY","controls":"PASSED_WITH_RETAINED_REPAIRS_AND_POSTCONTACT_ADAPTER",
      "work":"CONFIRMED_QUALIFIED_LOCAL_SOURCE_ENVELOPE_WITH_SEPARATE_FINAL_RECOVERY",
      "full_stored_type_body_record_bytes":sum(x["uncompressed_bytes"]for x in metas),
      "full_stored_type_body_gzip_bytes":sum(x["gzip_bytes"]for x in metas),"evidence":quality,
      "qualifications":["ExactChild is supplied exact/minimum/complete; no recursive solver implementation",
        "selected-Choice branch domain; arbitrary raw cuts/materialization not automatically valid",
        "retained-first prerelease vs cut-first actual literal order; adapter postcontact, no blind order credit",
        "CALL tuple mutations test request identity, not universal mathematical query inequivalence",
        "Lean relies on IH; Python validates returned partitions; no universal program equivalence",
        "local source counts, kernel meter algebra, compiled instructions and wall time are distinct",
        "formal final recovery charged separately by qualified finalPolynomial(S,G)*c^q",
        "installed Std/Init pinned, not rebuilt; toolkit-wide bootloops-check not run",
        "fresh-context framing remains separate"],
      "main_milestones":"ALL_OPEN","full_recursive_solver":"OPEN","global_work_induction":"OPEN","smaller_global_base":"OPEN","novelty":"OPEN"}
    put("SOURCE-REVIEW-SEAL-v1.json",seal)
    for r in files:(H/r["path"]).chmod(0o444)
    for n in["SOURCE-REVIEW-MANIFEST-v1.json","SOURCE-REVIEW-SEAL-v1.json"]:(H/n).chmod(0o444)
    print(json.dumps({"seal":str(H/"SOURCE-REVIEW-SEAL-v1.json"),"seal_sha256":sha(H/"SOURCE-REVIEW-SEAL-v1.json"),"manifest_sha256":seal["source_review_manifest_sha256"],"members":len(files)}))
if __name__=="__main__":main()
