# Final-release review

Parent released completed transport/assembly after the initial partial report.
Initial reports, independent checker, frozen controls and source copies remain unchanged.
Release pointer: FINAL-REPLAY.json -> replay/20261014T145838Z/receipt.json,
expected SHA256 7b6cea342c8b72c04907643d7075c5bdd36758950e83d0e10af72732aef3fa43.

READ: ActualRefinement.lean 13–39 composes actual_one_tree_split,
restrictionAgrees_subset, actual_support_mono in u and actual_disjoint_transport.
It has no transport hypothesis. Exact numeric degree supplies occupied membership.
Only t full-label uniqueness, B Nodup/inclusion in t, B restriction agreement,
and exact degree two are needed, so the stronger original pin hypotheses suffice.
READ: ActualRefinement.lean 43–65 starts with original agreement and arbitrary
per-tree old marks, obtains block premises from AgreementBlock, and returns
original agreement, avoidance, both old marks and exact component/cut increments.
The component form 69–87 explicitly retains B subset S, B occupancy and B
nonterminal. RefinementControls invokes those general theorems on the quartet,
prior old marks, component degree and unequal-full-label examples; 52–53 also
rejects cross-tree address identity.

Pending: inspect all transport sources; verify final receipt and source/log pins;
fresh full replay and axiom/false-control inventory; renewed consumer ruling.
READ: RestrictionTransport.lean 23–51 proves exact option-valued restriction associativity by intersection and then subset associativity; 74–86 derives restriction preservation from RootedIso induction, including swapped children. `restrictionAgrees_subset` (108–135) uses an occurring selected label for nonemptiness and transports through actual original `sameShape_correct`; no full-tree label equality or address identity is assumed. SupportAlgebra.lean 5–9 identifies Apart with original disjointVertices; shell algebra 59–66 decomposes actual root/left/right address disjointness. Inline simp-attributed theorem declarations exist in this release and must be included by the final explicit-declaration parser.
READ: SupportProfile.lean 55–70 defines five actual Boolean tests: two rooted-span emptiness tests and three rooted/minimal pair disjointness tests. The structural recursion is proved from exact shell equalities (85–103), not posited as a new agreement predicate. ActualSupportTransport.lean 38–70 proves profile invariance under actual restriction with A,C subset B, explicitly handling both unary-suppression cases. Lines 73–80 prove RootedIso invariance by structural induction and sibling commutation. Lines 85–110 extract original minimalVertices/disjointVertices equality through the two actual restricted trees and original sameShape_correct. Therefore equality is of intersection tests, never equality of addresses or supports between input trees. Lines 114–123 combine this with hereditary block agreement. All are derived lemmas; the final assembly calls them without an unproved transport parameter.

Final rebuild first attempt passed: all 24 released sources, complete fresh named
axiom inventory, exact match to author scoped declaration inventory, 16 explicit
false controls, malformed excluded. The final receipt pointer, all released
source pins and every author source/log binding matched. Circularity check found
an acyclic import graph with only released sources and Std; final local theorem
has no transport hypothesis. Full source provenance and diagnostics retained in
rebuild_final_receipt.json and build_final/. No proof file modified.
