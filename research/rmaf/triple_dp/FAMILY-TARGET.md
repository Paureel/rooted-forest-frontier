# Region-family target — 2026-10-14

Continue G2 from the completed single-region address theorem. The precise
debt is recorded in PROOF.md under "Precise formal debt G2" and "next G2".
Prove cost-preserving soundness/completeness directions, not a raw-support
bijection. Unrestricted rMAF and a smaller exponential base remain open.

Pin a finite labelled binary-tree vertex model. A family has pairwise
disjoint path-convex supports, covers every relevant leaf exactly once, and
each charged region contains at least one label. Each closed region can be
trimmed to its block's minimal span; the one open region can be trimmed to
that span plus the stem to the subtree root. Prove trimming preserves labels,
disjointness and block count. Then prove restriction/assembly through the
four existing transitions preserves these properties and closing charges.
State explicitly how any leafless open fragments are discarded; they may
not silently become charged blocks or new boundary states.

May assume: the audited generic min-plus and ConnectedRegions theorems with
their stated hypotheses. Must not assume family assembly, trimming, cost
preservation, graph-to-DP correspondence, or Python correctness. Preserve
all existing definitions, evidence and frozen receipts; new modules and
separate receipts must not inflate the original counts.

Adversary-first controls must include the existing gapped LCA-closed support,
the two supports that differ by a leafless child incursion, singleton/root
boundaries, an unused internal vertex, and adjacent same-color regions that
must remain separate. Reuse of known examples is regression evidence, not
holdout. Freeze additional independent controls before construction. If the
stated normal form fails, retain the exact counterexample and write the
corrected interface with its weaker acceptance boundary.

An acceptable partial result is a universal trimming or family assembly
lemma with all remaining links explicit. Prefer proving the shared invariant
over expanding the existing finite census. Before acceptance obtain fresh
semantic/axiom/control review; require actual false-proposition diagnostics
and a matching positive twin.

Own `family/`, receipts `../results/triple-family-*`, and progress
`../progress/triple-family.json`. Executable RMAF hull extraction is assigned
separately to the completed bridge review arm. Thesis audits are independent.
