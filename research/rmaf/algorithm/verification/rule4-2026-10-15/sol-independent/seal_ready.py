"""One-shot deterministic prerelease seal; creates no candidate authorization."""
import datetime,hashlib,json,pathlib,os
H=pathlib.Path(__file__).resolve().parent
ROOT=next(p for p in H.parents if(p/"bootloops-python").exists())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(name,obj):(H/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+"\n")
def main():
    for name in ["READY-v1.json","PRERELEASE-MANIFEST-v1.json","CONTACTS-v1.json"]:
        if(H/name).exists():raise RuntimeError("immutable seal already exists: "+name)
    public=["research/rmaf/algorithm/verification/rule4-2026-10-15/TARGET-v1.md",
      "research/rmaf/algorithm/verification/ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md",
      *["research/rmaf/algorithm/universal233/rule4/"+n for n in ["TARGET-v1.md","RESULT.md","INTERFACE.md","COST-MODEL.md","FIRST-GAP.md"]],
      "research/rmaf/algorithm/verification/both-bad-2026-10-15/PUBLIC-DEFINITIONS-v1.json"]
    skills=[".agents/skills/"+n+"/SKILL.md" for n in ["prove-protocol","reading-contract","independence-bookkeeping","planted-truth","timing-discipline","tool-stewardship","acceptance-gate"]]
    toolkit=["bootloops/tools/README.md","bootloops/tools/gatekeeper/GUIDE.md","bootloops-python","activate.sh"]
    installed=["Lean/Environment.lean","Lean/Declaration.lean","Lean/Util/FoldConsts.lean"]
    installed=[".runtime/elan/toolchains/leanprover--lean4---v4.35.0/src/lean/"+p for p in installed]
    contacts={"phase":"PRE-CANDIDATE","public_contacts":[{"path":p,"sha256":sha(ROOT/p)}for p in public],
      "skills":[{"path":p,"sha256":sha(ROOT/p)}for p in skills],
      "toolkit":[{"path":p,"sha256":sha(ROOT/p)}for p in toolkit],
      "installed_Lean_API_sources":[{"path":p,"sha256":sha(ROOT/p)}for p in installed],
      "order":"TARGET read first, skeleton saved immediately; initial skill batch truncated then repaired by individual full reads and incremental notes. Public reading/contact sequence and all failure repairs are in REVIEW-SKELETON-v1.md. Hash-only seal recontacts same permitted bytes.",
      "own_prior_reuse_before_review":"none",
      "own_reuse_within_review":["child_controls imports own original_graph; same route, no second-route claim","source_adaptation_controls imports own producer_controls validator; same detector, no second-route claim"],
      "forbidden_contacts":[],"candidate_contact":False,"other_verifier_contact":False,"author_program_contact":False,"children_spawned":False}
    write("CONTACTS-v1.json",contacts)
    files=[]
    for p in sorted(H.rglob("*")):
        if not p.is_file() or "__pycache__"in p.parts or p.suffix==".pyc":continue
        files.append({"path":str(p.relative_to(H)),"bytes":p.stat().st_size,"sha256":sha(p)})
    manifest={"schema":"rule4-independent-prerelease-v1","utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"files":files,"excluded":"__pycache__/*.pyc runtime caches only; no scientific/candidate files"}
    write("PRERELEASE-MANIFEST-v1.json",manifest)
    fixture=json.loads((H/"fixtures-output-v2.json").read_text())
    ready={"status":"READY_AWAITING_EXACT_ROOT_RELEASE","candidate_contact":False,"self_release":False,
      "manifest_sha256":sha(H/"PRERELEASE-MANIFEST-v1.json"),"manifest_files":len(files),
      "author_manifest_pin_only":"6f38a6930b5f3794207a66c93a890d5e89d4a6562d820d291533ae58b2f50940",
      "counts":{"construction_controls":32,"finite_child_controls":153,"literal_callback_tuples":9,"producer_controls":32,"actual_source_adaptation_controls":5},
      "fixtures":[{"name":f["name"],"partitions":f["partition_count"],"original_agreements":len(f["agreements"]),"minimum_components":f["minimum_components"],"choices_with_traversal_orders":len(f["choices"])}for f in fixture["fixtures"]],
      "failure_ledger":"REVIEW-SKELETON-v1.md failures001–006 retained; source/output artifacts retained",
      "postrelease_plan":"POSTRELEASE-PLAN-v1.md","verdicts":{"semantic":"OPEN","interface":"OPEN","candidate_provenance":"OPEN","candidate_source_work":"OPEN","main_milestones":"all OPEN"},
      "finite_result_scope":"bounded NOFIRE and independent instrument controls only; no universal proof or scientific acceptance"}
    write("READY-v1.json",ready)
    for r in files:(H/r["path"]).chmod(0o444)
    for n in ["PRERELEASE-MANIFEST-v1.json","READY-v1.json"]:(H/n).chmod(0o444)
    print(json.dumps({"ready":str(H/"READY-v1.json"),"ready_sha256":sha(H/"READY-v1.json"),"manifest_sha256":ready["manifest_sha256"],"files":len(files)}))
if __name__=="__main__":main()
