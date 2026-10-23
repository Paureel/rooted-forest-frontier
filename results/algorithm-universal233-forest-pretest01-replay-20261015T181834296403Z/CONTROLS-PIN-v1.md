# Forest pretest controls v1

Pinned before new code/instrument use. Author development only.

1. Internal target overlap: T=((0,1),(2,3)), sources [(0,2),(1,3)].
The unchanged source partition fails target clearance, while cutting either
original edge in source0 gives actual AF [[0],[2],[1,3]] of cost1. Both
ordinary component pairs have local cost0; their chosen minima do not solve
the full state. Mirror target and source sibling orientations explicitly.
2. Reject cost≤1: T=((0,1),((2,3),(4,5))), sources [(0,2),(1,4),(3,5)].
Every pair of unchanged source hulls overlaps. One source edge cannot clear
all pairs; splitting two sources gives a retained actual cost2 witness.
3. None/empty is proper and resolves cost0; singleton/singleton resolves0.
None/nonempty, target/nonempty labels mismatch, duplicate target/source labels
and missing sources refuse as malformed.
4. Missing-edge plant: omit every edge from source0 in control1. The specific
actual cost1 forest [[0],[2],[1,3]] must then have no inner/outer-Perm-equal
candidate, even if a different cost1 forest can still be found. This tests
universal exact coverage, stronger than mere existence of a cheap answer.

Use actual original ForestState.agrees in Lean for every executable control.
Kernel decide is allowed; no native_decide/axiom/admit/sorry. Pilot bound30s
per Lean module; initial final-replay runtime unknown and measured as modules
complete. Finite controls are not universal source-edge coverage proofs.

Final fresh Std-only producer controls precede scientific audit: clean twins
and hostile same-name/type custom axiom+own clean declaration in both orders,
private/unused axioms, false proofs, missing/duplicate rows, wrong module path
and source/adapted-byte corruption. Audit all stored producer occurrences.
No toolkit-wide suite or old census. State source primitive/bit/payload limits.
