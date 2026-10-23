# Connected-region wrapper replay

The workspace-wrapper replay passed using `bootloops-lean` with workspace ELAN_HOME. It rebuilt the isolated sources and checked the same eight extension theorems, 19 dependency theorems, false-path-vertex rejection, and passing clean twin. The four builds took 1.5432849589997204 seconds. The original direct-binary receipt and logs retained their hashes.

Only the execution launcher changed; scientific source contents, control contents, and check logic were retained. New receipt, log, and build-output paths preserve the original replay. Lean reported version 4.35.0, and the theorem names, axiom lists, and return codes match the first replay exactly.

Details are retained in `triple-dp-verification-connected-wrapper.json` and `triple-dp-verification-connected-wrapper-comparison.json`. The earlier scope review remains applicable: the extension proves single-region path-convex address decomposition, while the labelled-family and cost-preserving G2 correspondence remains OPEN.
