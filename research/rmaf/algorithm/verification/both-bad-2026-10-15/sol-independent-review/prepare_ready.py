#!/usr/bin/env python3
"""Validate named prerelease artifacts and create an immutable hash inventory.

Reads only owned evidence, target/public-definition/statement/skill/tooling paths.
It never reads the candidate manifest or candidate source tree.
"""
import hashlib
import json
import os
import pathlib
import time

HERE=pathlib.Path(__file__).resolve().parent
ROOT=pathlib.Path("/Users/paurel/Documents/ChatGPT/bootscience")


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(name): return json.loads((HERE/name).read_text())
def write(name,value): (HERE/name).write_text(json.dumps(value,indent=2,sort_keys=True)+"\n")


def main():
    assert not (HERE/"READY-v1.json").exists(), "READY cannot be regenerated in place"
    bank=read("bank-v2.json")
    assert bank["status"]=="PASS" and len(bank["cases"])==25
    assert sum(r["refiner_denominator"] for r in bank["cases"])==13650
    assert read("plants-v2.json")["truth"]["denominator"]==10
    assert read("plants-v2.json")["ledger"]["denominator"]==23
    assert read("toy-results-v1.json")["status"]=="PASS"
    assert len(read("toy-results-v1.json")["plants"])==10
    assert read("producer-results-v2.json")["status"]=="PASS"
    assert len(read("producer-results-v2.json")["plants"])==9
    assert "Tactic `decide` proved that the proposition\n  0 = 1\nis false" in (HERE/"toys/ToyFalse.build.log").read_text()
    full=read("toys/AuditProducerFull-stored.json")
    assert len(full["stored_occurrences"])==33 and len(full["resolved_names"])==33
    assert len(full["rejected"])==3
    assert any(r["name"].endswith("privateSeed") and r["body"] is not None for r in full["stored_occurrences"])
    assert any(r["name"]=="ToyGenerated.Cell.rec" and r["kind"]=="recursor" for r in full["stored_occurrences"])
    assert any(r["name"].endswith("ToyPrivate.producer") and r["body"] is not None for r in full["stored_occurrences"])
    assert sum(len(p["compiler_extra_names"]) for p in full["producer_inventories"])==6
    supplement=read("supplemental-v2.json")
    assert supplement["status"]=="PASS" and supplement["callback_minima"]==[3,1,2]
    capsule=ROOT/"research/rmaf/algorithm/verification/both-bad-2026-10-15/PUBLIC-DEFINITIONS-v1.json"
    assert sha(capsule)=="c413d7437ef472976dbdeffc432401fbed88ba1d71c51e7822022fcb776e29ac"
    public=json.loads(capsule.read_text())
    contacts=[]
    def contact(path,scope,role):
        p=ROOT/path if not pathlib.Path(path).is_absolute() else pathlib.Path(path)
        contacts.append({"path":str(p),"scope":scope,"role":role,"sha256":sha(p)})
    contact("research/rmaf/algorithm/verification/both-bad-2026-10-15/TARGET-v1.md","full; FIRST scientific file read","root target pin")
    for name in ["prove-protocol","reading-contract","independence-bookkeeping","planted-truth","timing-discipline","tool-stewardship","acceptance-gate"]:
        contact(".agents/skills/"+name+"/SKILL.md","full; individual reread after initial output truncation","required skill")
    contact("bootloops/tools/README.md","full index plus capability search","toolkit capability consultation")
    contact("bootloops/tools/gatekeeper/GUIDE.md","full","nearest integrity guide, no toolkit engine used")
    contact(str(capsule),"full exact excerpt capsule only","root-whitelisted public definitions; not candidate release")
    for p in public["public_statement_whitelist"]:
        contact(p,"full","public statement, not proof/implementation")
    contact("research/rmaf/algorithm/verification/ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md","full","public detector requirement; referenced reviewer implementation NOT opened")
    for p in ["bootloops-lean","bootloops-lake"]:
        contact(p,"full","local compiler wrapper")
    compiler=".runtime/elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Lean/"
    for p,scope in [("Environment.lean","API searches and ranges109–180,1186–1218,2430–2482; whole-file SHA only"),
                    ("Declaration.lean","type/value/kind API name search; whole-file SHA only"),
                    ("Util/FoldConsts.lean","full compiler API")]:
        contact(compiler+p,scope,"compiler/library tooling API, no scientific verifier reuse")
    excerpt_contacts=[]
    for src in public["sources"]:
        excerpt_contacts.append({"original_path":src["path"],
          "original_whole_sha256_from_capsule_unverified_until_release":src["source_sha256"],
          "ranges":[{"start":r["start"],"end":r["end"],"excerpt_sha256":hashlib.sha256(r["text"].encode()).hexdigest()} for r in src["ranges"]],
          "contact":"excerpt text only via public capsule; original file not opened"})
    write("CONTACT-LEDGER-v1.json",{
      "contacts":contacts,"original_excerpt_contacts":excerpt_contacts,
      "metadata_only_contact":"One overly broad filename listing exposed results/*.lean/*.olean names; no contents opened or used. Preserved in PREPARATION.",
      "code_reuse":"v2 graph/supplement and producer utilities reuse own earlier arm code only. Public source CoreProgram definitions read as permitted semantics; no candidate both-bad planner/dispatcher or previous verifier implementation read.",
      "candidate_contact":False,"author_reviewer_contact":False,
      "deepest_shared_layer":"Public mathematical definitions and public source-core rule/priority specification. Independent code uses original graph BFS/induced clades and surviving-leaf prefix reconstruction. This is not independent statistical replication."})
    write("PREP-CHECKS-v1.json",{
      "status":"PASS","bank_cases":25,"source_refiners":13650,
      "truth_controls":10,"ledger_corruptions":23,"resolved_adapter_corruptions":10,
      "stored_occurrence_corruptions":9,"full_toy_stored_occurrences":33,
      "full_toy_resolved_names":33,"compiler_extra_names_inventoried_not_kernel_bodies":6,
      "root_erratum":"selector vertex00 confirmed; advertised edge fails sector clearance",
      "S11_callback_minima":[3,1,2],"candidate_review":"NOT_RELEASED"})
    failures=[
      "Initial batched skill reads truncated output; individual full rereads completed before governed calculation.",
      "Root-proposed initial tree is a vertex-selector boundary, not selected-edge regime; immutable erratum preserved and independently confirmed.",
      "Metadata-only wrapper discovery was overly broad; no listed scientific contents opened.",
      "Two SHA preflight shell commands used incorrect cwd-relative paths; source/preregistration texts already existed, hashes recorded immediately without edits; cold source rebuilds passed after hash freeze.",
      "v1 merged-name origin gate falsely accepted coalesced hostile stored axiom. Fresh stored-producer gate caught it; original gate scope and results preserved."]
    write("RETAINED-FAILURES-v1.json",failures)
    files=[]
    excluded=[]
    for p in sorted(HERE.rglob("*")):
        if not p.is_file(): continue
        rel=str(p.relative_to(HERE))
        if "__pycache__" in p.parts or p.suffix==".pyc":
            excluded.append(rel);continue
        if rel in {"READY-v1.json","READY-v1.sha256"}: continue
        files.append({"path":rel,"bytes":p.stat().st_size,"sha256":sha(p)})
    ready={
      "status":"IMMUTABLE_READY_PRE_CANDIDATE_AWAITING_SEPARATE_ROOT_RELEASE",
      "created_unix":time.time(),"scope":"Independent preparation only, no candidate acceptance",
      "directory":str(HERE),"files":files,"transient_exclusions":excluded,
      "release_required":{"root_separate_RELEASE":True,"author_payload_entries":560,
        "author_manifest":"BOTH-BAD-MANIFEST-v1.json",
        "author_manifest_sha256":"da001ef62039c916cf6db24f61c994094b5b1750f5be9130ddaf512ae5fbe20d",
        "candidate_manifest_opened":False},
      "candidate_verdicts":{"semantic":"OPEN_NOT_CONTACTED","consumer":"OPEN_NOT_CONTACTED",
        "actual_control":"OPEN_NOT_CONTACTED","work_model":"OPEN_NOT_CONTACTED","provenance":"OPEN_NOT_CONTACTED"},
      "acceptance_limits":["No universal theorem closure from finite bank","No complete recursive solver from fixed child tables",
        "No compiled instruction identity or callerUnit correspondence","Compiler extra names inventoried separately from kernel ConstantInfo bodies",
        "No full algorithm, mutual well-founded recursion, global exponent/base or novelty closure","No independent statistical replication claim"],
      "retained_failures":"RETAINED-FAILURES-v1.json",
      "post_release_policy":"Never edit frozen READY files; create separately named new review outputs. No self-release."}
    write("READY-v1.json",ready)
    digest=sha(HERE/"READY-v1.json")
    (HERE/"READY-v1.sha256").write_text(digest+"  READY-v1.json\n")
    for row in files:
        p=HERE/row["path"]
        assert sha(p)==row["sha256"]
        p.chmod(p.stat().st_mode & ~0o222)
    for name in ["READY-v1.json","READY-v1.sha256"]:
        p=HERE/name;p.chmod(p.stat().st_mode & ~0o222)
    print(json.dumps({"status":ready["status"],"READY_sha256":digest,"files":len(files),
                      "checks_sha256":sha(HERE/"PREP-CHECKS-v1.json"),
                      "contacts_sha256":sha(HERE/"CONTACT-LEDGER-v1.json")}))


if __name__=="__main__":main()
