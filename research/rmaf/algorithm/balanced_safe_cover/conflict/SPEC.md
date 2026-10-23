# GLOBAL-C frozen specification, v1

Frozen before construction tests: 2026-10-14.

## Source and target

Read source: `research/rmaf/sources/previous-work/RESEARCH.md`, Sections 1, 2, 4, 6, 8, preserved source hash `960bff1cb96bf7501e2dc27c23cb5b29303378816d9b7249a5740151706e3865`.

Verbatim Section 8 target: "Given a reduced rooted tree pair and cut budget b, construct in O*(1.25^b) time at most O*(1.25^b) source-forest refinements F_j" with counted nonredundant source cuts, survival of at least one original optimum, pure-bridge or compatible/triple membership, and original ordinary local distance at most b/2 in every pure-bridge output. This is explicitly a research target in the source.

Ordinary rooted unordered binary labeled trees, distinct common label set, no implicit rho. Restriction suppresses unary nodes. Convexity uses vertex-disjoint unsuppressed minimal supports. Empty and singleton inputs are permitted controls. Reductions and label reconstruction remain obligations for any reduced-instance consumer.

## Organizing constituent

Source-edge conflict hypergraph H(S,T), computed directly on original unsuppressed source edges:

1. For each three labels with incompatible rooted restrictions, include every edge in their minimal source span as one hyperedge.
2. For every two disjoint label pairs whose source paths are vertex-disjoint and whose target paths meet, include the union of the two source-path edge sets as one hyperedge.

Candidate theorem C1: a source cutset induces an agreement partition iff it hits every hyperedge. Cuts that leave unlabeled components are normalized away before counting; partition cut cost is number of nonempty components minus one.

Candidate theorem C2: pairwise edge-disjoint conflict hyperedges lower-bound every feasible cutset by their count. If a supplied transversal attains this bound, its agreement forest is optimum and every normalized subset of its cuts preserves that optimum. This is a polynomial certificate, not a procedure for finding the transversal.

Falsifiable candidate C3: maximum disjoint conflict packing equals rMAF cut optimum. Freeze a potential smallest obstruction: S=((a,b),(c,d)), T=((a,c),(b,d)), expected optimum=2, expected maximum packing=1. A fire rejects C3 only; it does not reject C1/C2 or safe-cover existence.

## MAY ASSUME

- Basic finite tree connectivity and uniqueness of paths.
- Distinct labels and rooted binary restrictions as defined above.
- Frozen X0 receipts as finite external evidence, with their exact declared scope.
- Pure-bridge G1-G7 and triple G1-G3 only as conditional graph/executable imports. They do not certify the ordinary input correspondence in this route.

## MUST NOT ASSUME

- That a balanced source edge preserves an optimum.
- That independent mark penalties add.
- That hypergraph packing is tight or that lower bounds determine a safe branch.
- That a supplied optimum or a distance oracle is available to the proposed algorithm.
- That exact tests establish a universal characterization or cover bound.
- That polynomial recognition gives polynomial generation of optimum transversals.
- That a conditional Lean combinatorial theorem discharges source-model semantics.

## Alternatives and downgrade

Exact cover: alpha=5/4, theta=1/2, all costs paid. Licensed weaker cover: alpha=3/2, theta=1/2, classical local c=1+sqrt(2), all costs paid. Any other alpha/theta requires a versioned preregistration before tests and exact certificate alpha*c^theta<2.3391. No such alternative is adopted in v1.

If C1 fails, retain the exact witness and revise the hypergraph in v2. If C3 fails, use packing only as a lower-bound certificate. If the source-model trace or runtime cannot be proved, report the exact open lemma; do not close Algorithm, Correctness, or Smaller base.

## Frozen controls and gates

`controls-v1.json` is the literal preregistration. Run all fixtures and every comparator mutation before censuses. Any mismatch halts the run; no expected-value rewrite. Exact cut-subset enumeration and an independently organized set-partition enumerator are test oracles only. Their shared tree primitives weaken their differential independence; a fresh nonauthor rebuild remains required.

Pilot all n<=4 tree pairs before any larger census. A pilot must record input count, elapsed time, exact mismatch count, and witness size; no unchecked ETA. Keep raw receipts and scripts. A bounded n<=5 census is licensed only after the measured projection is under two hours.

## Oracle contact log

- 2026-10-14: read X0 controls-v3 and equal-halfbudget-n4 receipt. These values now influence GLOBAL-C construction and cannot independently certify GLOBAL-C's derived generator.
- 2026-10-14: control expectations below use by-construction topology arguments plus the literal X0 witness. This is declared reproduction, not independent certification.

## Toolkit consultation

Read `bootloops/tools/README.md`; searched `toolkit/ours/README.md`, `RECIPES.md`, and external engine index for agreement forest, rooted tree, conflict and separator capabilities; no matching combinatorial evaluator exists. Gatekeeper's data-integrity/CV scope does not implement exact finite-tree semantics. A one-shot local exact enumerator is therefore justified; upstream instruments remain unchanged.
