# Source reconstruction journal

Source is Chris Whidden, *Efficient Computation and Application of Maximum Agreement Forests*, July 2013 thesis, local PDF. Printed page p is PDF page p+13 (1 based). Local extracted text omits PDF pages 121/123/131; those images are inspected separately.

## Read

- Chapter 2 printed pp12–18: rho is a labelled unary root and part of X; forests are cut and suppressed; q (thesis k) counts cuts and m=q+1 components. No unaugmented transfer is claimed here.
- All Chapter 6 text printed pp100–127 opened in this session; images recover missing pages.
- Printed p110, Fig6.4: protected edges of active F1 are pendant to a single root-leaf path and their bottom endpoints lie in Rt. Eligible sibling pairs descend from the deepest top endpoint of a protected edge. Choose maximal F1 depth, then separate F2 components or maximal deepest-member F2 depth. Remaining ties arbitrary. This is a restriction on reachable transitions, not optional tie-breaking.
- Printed p111, Fig6.5: failure k<0 before success |Rt|≤2, then sibling reductions, then ordered branch cases. The figure prints SC where preceding definitions say AC; this naming discrepancy is retained.
- Printed pp116–117, Thm6.13: per invocation O(n) is asserted by adaptation of [101,102]. The proof introduces analysis-only sets Q⊆P, |P|≤2, with bound I(k,P,Q)≤alpha*(2^(k-|P|)+|Q|2^(k-|P|-1))+|P|-3.
- Printed p118, Fig6.6: G1 is current invocation; G2 inside d; G3 pair(a,d); G4 inside e; G5 pair(a,e); G6 outside r. The group induction requires later-group credited states and smaller-k uncredited states. G1 C-child creates P={a}; Q empty in A2BC and {a} in A3BC.
- Printed pp119–121: G2 maintains outer credit or creates a second credit. G3 claims credited a,d cannot have merged; double-protected pair has ≥2 pendant edges. These are geometric reachability obligations.
- Printed pp122–123: G4 inherits the G1–G3 analysis by union with existing P′,Q′. Exception: in a G4.1 A3BC B-child, reset both sets to empty; Case2B also resets both. This exception requires a fresh arithmetic check; it is not an identical recurrence.
- Printed pp123–126: G5 argues non-merging, no two-child A2/A3 when incoming P={a},Q=empty, and two protected endpoints imply dead end or ≥2 pendant cuts. G6 receives no outstanding credit.

## Inferred / open

The target bound is a credit potential with normalized weight W(p,q)=(2+q)/2^(p+1), additive offset p-3, and p=|P|,q=|Q|. A transition dropping cut budget by d contributes W(p_child,q_child)/2^d. Arithmetic and reachable-state restrictions are being checked separately.

Tool consultation: bootloops/tools/README.md plus toolkit capability index/recipes contain no rooted-tree reachability or finite branching-potential checker. New one-shot campaign scripts will use exact Python Fraction arithmetic and Lean's local standard library; they are not additions to upstream toolkit.

## Provenance

No correctness-arm or convention-transfer implementation read. Hand controls were authored before the recurrence evaluator; they certify its arithmetic comparison only. Python and Lean formalizations will share the manually transcribed mathematical transition list; they are not independent validation of that list. Fresh semantic review remains the parent's separate stage.

Erratum 2026-10-14: The initial source-notes title was incorrectly reconstructed from memory; it has been corrected to the title read on PDF page1, *Efficient Computation and Application of Maximum Agreement Forests*. The original local PDF is unchanged. Author/institution/date were read from the same title page; no .bib entry is being created.

## Executed follow-up

The exceptional G4.1 r=0,s=3 transition is reachable on the nine-leaf trace retained in `thesis-complexity-reachable-trace.json`. A separate 13-leaf trace reaches the p=3 state under the G4 union instruction. `Trace.lean` checks concrete cuts, depths, predicates, and protection transport for both. `Credit.lean` proves the exact arithmetic discrepancy. Source theorem status remains open because the witness's C-child terminates and a stronger amortized proof may repair the source argument.
