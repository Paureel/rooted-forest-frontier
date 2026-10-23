from pathlib import Path
from hashlib import sha256
import json

H = Path(__file__).resolve().parent
ROOT = H.parents[5]
prior_rel = "research/rmaf/algorithm/verification/forest-reductions-2026-10-15/sol-frozen-ready-v1/preparation/CONTACTS-v1.json"
prior = ROOT / prior_rel
inherited = json.loads(prior.read_text())
out = {
    "phase": "all-good DP PRE-CANDIDATE controls only",
    "firstContact": "research/rmaf/algorithm/verification/all-good-dp-2026-10-15/TARGET-v1.md",
    "skeletonImmediatelyAfterRootPin": True,
    "newPublicScientificDefinitionReads": [],
    "inheritedDefinitionAndProtocolLedger": {"path": prior_rel, "sha256": sha256(prior.read_bytes()).hexdigest(), "records": inherited["records"]},
    "currentContacts": [
        "Root TARGET pin and own new workfile first; own frozen graph/checker/auditor source reuse as recorded in LINEAGE-v1.",
        "Toolkit README index capability rg search for rooted/phylo/dynamic/partition/graph; no suitable owner-color graph engine. Prior fully read applicable skills and emitall/gatekeeper guides remain in force.",
        "Own graph/checker extraction, original graph/path topology and partition oracle only; own prior source audit outcomes inform disclosed lazy-generation limitations.",
        "Own Std-only control sources and Lean validation APIs inherited from the prior ledger; findOLean path probe and exact Environment.header.moduleNames closure gate are validation-only APIs.",
        "Parent coordination only. No author, other-reviewer or child scientific contact.",
        "Integrity-only hash of all prior147/264 and77/103 artifacts, without scientific source/result interpretation."
    ],
    "rootPinSHA256": sha256((H.parent / "TARGET-v1.md").read_bytes()).hexdigest(),
    "definitionInterpretation": "Original-vertex minimal hulls and rooted suppression topology; State.Proper and agreement/current-source additional cost as pinned in the inherited public definition ledger. No new desired-consumer state field assumed.",
    "candidateContact": False,
    "candidateScientificCompilation": False,
    "barredContacts": {k: False for k in ["allGoodProof", "allGoodAuthorControls", "allGoodReceipt", "allGoodAuthorAuditor", "main", "genericForest", "ordinaryCherry", "outputState", "finalCut", "groups", "binaryCheap", "query", "classifier", "kept", "depth", "otherReviewerCode", "authorContact", "childAgent"]},
    "independentReplicaIncrement": 0,
    "freshContextProseRefereeCredit": False,
    "futureFreshContextReview": "Separate root assignment after the candidate source report is sealed."
}
(H / "CONTACTS-v1.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({"status": "CONTACTS-RECORDED", "newPublicScientificDefinitionReads": 0, "candidateContact": False}))
