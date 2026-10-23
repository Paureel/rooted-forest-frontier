# Preproof source controls v1

Pinned 2026-10-15 before author production theorems or control execution.

Actual original rooted Tree controls, using ordinary equal-label source pairs:
- t1: T=((a,b),c), S=((a,c),b). Exact outgoing path cut is c's original edge.
- t2 at root LCA: T=((a,b),(c,d)), S=((a,c),(b,d)). Exactly c,d cuts.
- t3: T=((a,b),(c,(d,e))), S=(((a,c),d),(b,e)). Exactly c,d,e cuts.
- upward root boundary: enclose t3 pair in a root with leaf f. The upward
  root-side arc is not an outgoing path pendant; f stays in residual core.
- sibling order: swapping the target cherry and source left/right orientations
  must preserve cuts' original meaning and safety, without making a rho label.
- strict t1 refinement failure F={{a,c},{b}}; valid no-larger replacement
  G={{a,b},{c}}. Both are actual agreements on the t1 pair; F does not refine
  the pendant partition. The exchange is required for deterministic t1 safety.
- false unpaid-cut: pendant t3 branch cost must be 3, not 2.
- false implicit-rho: residual original labels are exactly a,b,c,d,e (or f in
  the explicit enclosure), and no invented label appears.
- false source-disjointness: actual overlapping source spans must be rejected.
- false t1 strict-refinement and missing-root-boundary controls must fail.

Control failure stops the claim; a false proposition being accepted invalidates
its checker. Successful controls are development evidence, never fresh review.
Pilot: time a single Lean graph-control compile; no large census or raw receipt
volume is planned. Replay progress unit is completed source modules/audits.
