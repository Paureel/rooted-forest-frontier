# CB2/CB3 nonauthor transition design v1

Frozen before reading parent implementations or running new row compilations.
Read inputs: SPEC-CB2.md, SPEC-CB3.md, RESULT.md and the completed CB3
obstruction receipt. Expected scientific values are retrieved claims under
review, not independent data. No parent optimizer implementation was read.
The frozen CB1 adversary instrument is reused only for parsing, paths,
restrictions, partitions, H generation and the abstract column quotient.

Define implies(A,B) as: every row of B contains some row of A; empty CNF is
true. Check against literal Boolean satisfaction of every subset of the finite
original edge universe. Child i dominates j iff delta_i<=delta_j and
implies(rows_j,rows_i). Preserve one lexicographically lowest original-edge
representative of each mutual-equivalence class; discard strictly dominated
children. Order kept children by (delta,branch_edge,cut_mask,rows).

Closure repeatedly computes minimal-row maximal-column projection. If the
row set changes without a singleton, continue to a fixed point. Choose the
smallest singleton edge when available, record its ORIGINAL index, delete
all hit rows, and repeat. At fixed point return residual masks and distinct
forced original cuts. A child first selects its branch edge, filters hit
rows, then closes; delta equals one plus distinct forced cuts. This has no
budget, partition optimizer or distance query. Row compilation considers
every original edge of that row. CB3 mass is the exact Fraction sum(3/7)^delta.

Controls, executed before the ordinary reconstruction: empty closure0;
singleton [1] closes cost1; triangle [3,6,5] and four-of-five [15,23,27,29,30]
compile every row to one terminal cost2 child. Verify singleton/two-edge and
empty CNF implication in both directions, plus a clean cost/implication
child-dominance twin. Deliberately corrupt child delta by -1, mass numerator
by +1, duplicate an original cut index, reverse an implication assertion,
and omit a raw branch; each must reject, with clean twins passing. A false
7/3>=23391/10000 comparison must fail. Freeze exact control expectations in
CONTROLS-v1.json; controls write their receipt before any source scoring.

Then reconstruct the literal six-leaf source and target using the frozen
Tree class. Match original edge ids by their rooted descendant-label sets,
so unordered child orientation does not contaminate mask comparison. Build
all original conflict rows afresh. Independently enumerate set partitions
for optimum3 and all original source cutsets for C1 finite equivalence.
Rebuild closure, every one of 26 row compilations and every exact mass.
Compare raw and kept states, original prefix cuts/deltas and forcing steps
with the completed receipt. Exhaust Boolean assignments on the ten-edge
universe for every distinct child-state implication. Corrupt stored row,
delta and mass fields once and demand the comparison rejects each.

Only after all these runs read parent conflict_dag_solver.py,
conflict_row_selector.py, and necessary conflict_solver.py call sites to
trace semantic discrepancies and the consuming recurrence. No prior CB1
infinite-family proof is certified by this review. No broad census or long
compute is licensed. Run the six-leaf reconstruction as the measured pilot;
stop any individual leg exceeding10 seconds instead of silently extending it.

Text review: RESULT.md is authored by the parent. Audit its CB2/CB3 claims
with fresh referee-sim and prose-lint, separating correctness and novelty,
actual source C1 imports, finite arithmetic/source extraction, and caveat
prominence. Treat its CB1 proof as out of scope. No Lean verification is
claimed without actual source-bound compile and axiom logs plus false controls.
