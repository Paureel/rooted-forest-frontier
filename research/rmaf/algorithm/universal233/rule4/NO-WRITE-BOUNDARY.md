# Version 1 no-write boundary

RULE4-MANIFEST-v1.json identifies every immutable authored source, control,
interface/proof note, exact imported source hash and canonical replay file.
The named files are immutable. Repair requires a new version with a new
manifest and fresh result evidence; do not overwrite this release to satisfy a
review. Earlier frozen source packages, targets and results remain unchanged.

Replays create fresh results/algorithm-universal233-rule4-* directories. They
read SOURCE-INPUTS-v1.json and the frozen sources, and leave version-1 owner
files unchanged. Derived dev/*.olean/ilean/pyc and __pycache__ files are outside
the immutable set and cannot replace exact-source evidence.

Full stored producer kind/type/body/reference records are retained losslessly
in the canonical replay's occurrences.json.gz. occurrence-storage.json gives
the exact decompressed SHA256 and byte count, archive SHA256 and roundtrip
check. Decompress that archive to recover the exact occurrences.json audited
by the recorded run; the data were not reduced to resolved names or hashes.

The manifest itself is identified by RULE4-MANIFEST-v1.sha256 and the parent
handoff message. Fresh nonauthor semantic/interface/source-cost/prose review
remains pending. No author-side mutation after freeze may be called a fresh
independent verification. All three main algorithm milestones remain OPEN.
