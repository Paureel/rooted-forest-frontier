# Independent graph verifier

What: constructs explicit rooted binary adjacency graphs; calculates unsuppressed hulls by breadth-first paths; enumerates set partitions and pruned rooted restrictions. It tests deepest-root neighbor geometry, both avoidance directions, two-region splitting and old-mark preservation, and mark/region containment on bounded instances. It also reproduces the supplied finite multi-mark interaction.

When: adversarial finite verification of the pure-bridge interfaces. This purpose-specific verifier intentionally has no imports from the campaign oracle or original pure-bridge implementation. It is not an unrestricted MAF solver or a complexity certificate.

Output: exact integer counts and elapsed seconds in a retained JSON receipt. `finite-no-fire` means only all checked finite cases passed; any failed assertion terminates without that result. It does not mean a universal graph theorem or algorithm bound.

Acceptance: frozen CONTROLS.md plus its pre-execution erratum must pass; deliberately perturbed expected integers and the suppressed-path and leafless-region faults must be caught. Controls are exact hand values; no tolerance. A Lean proof and fresh semantic review are still required for general claims.

Run: `./bootloops-python research/rmaf/bridge_review/independent_graph.py --max-n 3 --output research/rmaf/results/bridge-review-pilot.json`.

2026-10-14: first implementation, after toolkit consultation and control freeze. No existing campaign engine modified.

`local_interfaces.py` checks source-side split transport and exact marked/region feasible partition identities, including fresh address reconstruction of suppressed region trees. `completion_interfaces.py` reconstructs the proposed elimination from its statement and checks every tie choice against exhaustive global partitions. These scripts share this review's graph core and are not independent checks of that core. Their receipts state the completed denominator; a pilot covers only its specified limit, even when the scope paragraph describes the full case pool.

`audit_lean.py` rebuilds the existing PureBridge dependency into the owned audit directory, then checks GraphRegion and GraphControls, logs all reported axioms, hashes sources, and demands failures of three false examples. A successful build certifies the printed graph theorem only. It does not supply an executable embedding extractor or the missing exchange fields.
