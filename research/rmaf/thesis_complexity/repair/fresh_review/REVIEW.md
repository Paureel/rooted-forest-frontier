# Fresh independent G4 runtime repair review

Status: conditional; review completed at the scopes in RULING.md. No unconditional source-state theorem accepted or rejected.

This nonauthor review began by reading `../FRESH-REVIEW-TARGET.md` before any proof-route details. Its implementation will be newly written from original source interfaces and exposed calibration data. No prior checker will be imported. All controls are exposed calibration; finite checks will not be reported as held-out theorem verification.

## Planned evidence boundaries

1. Reconstruct original Chapter 2/6 source interfaces and maintain a source-read ledger.
2. Freeze and run hand controls, corruptions, and orientation twins before inspecting candidate proof details.
3. Inspect adversary, geometry, and recurrence claims separately and grade their logical scope.
4. Rebuild decisive witnesses from explicit data, audit exact use sites and credit/physical-protection distinctions.
5. Independently check final Lean compilations and axioms, preserving failed attempts.
6. Report the smallest remaining falsifiable structural lemma, finite scope, and limitations.

## Source reconstruction

Pending.

## Exposed calibration and corruption controls

Pending.

## Candidate rulings

Pending; no candidate details read yet.

## Use-site composition and remaining obligation

Pending.

Source ledger entry 1 — read: original thesis text PDF p25, printed p12 (Chapter 2). The augmented root is a labelled unary node, distinct from all ordinary leaf labels; the text says “we consider ρ to be part of X.” Suppression deletes unlabelled nodes with fewer than two children, reconnecting degree-two parent/child neighbors. Thus a symmetric extra rho leaf may be used only with an explicitly stated equivalence, not silently treated as the literal source representation.

Tool selection: the toolkit index and `trust/GUIDE.md` were read. `trust` checks linear-reduction witnesses and cannot replay rooted-forest reductions; this one-shot nonauthor evaluator is therefore new code, explicitly required by the independent-review pin. It will use standard-library exact fractions and tree operations only, sharing source/control inputs but no prior checker code.

Source ledger entry 2 — read: printed pp107,109–111 / PDF120,122–124, including rendered PDF123 because its extracted text is empty. Branch cut-set legality is evaluated on the original forest: no protected edge and no root-incident edge with protected sibling may be in the simultaneous set. Suppression carries protection from either surviving incident edge. A3BC C protects `ea` in both forests, then cuts `ec`; B cuts all pendants at once. Physical protection may be arbitrarily numerous (printed p106 explicitly contrasts earlier one-edge protection). Priority is SC/AC, B, RB, RB*, 2B, BCY, A2BC, A3BC. BCY second branch cuts `{ec,ey}` at cost two. The depth rule first restricts beneath the deepest protected-edge parent in F1, then maximizes F1 depth; ties prefer separate components or greater deepest F2 depth. The page says “Remaining ties are broken arbitrarily.” Failure at negative k precedes success; common sibling contraction and singleton-root removal loop within the invocation.

Source ledger entry 3 — read: printed pp116–117,119–122 / PDF129–130,132–135. Theorem 6.13 claims O(2^k n); the potential printed on p117 is alpha*(2^(k-|P|)+|Q|*2^(k-|P|-1))+|P|-3, while P is declared to have at most two members. Its displayed recurrences count `1` for the current invocation despite calling I the number of descendants. The p117 negative-budget footnote covers only -3..-1 and uses surrogate decrements; actual q-edge B batches can be larger. G2 (p119) and G3 (pp120–121) have both reset-to-empty and continued-credit branches, requiring their own structural facts. In G4 (p122), unary branches reset; BCY resets both cost-at-least-two children; other two-child branches retain credits. The text asserts its active local subtree has at most four leaves. These are source statements, not independently certified invariants.

Source ledger entry 4 — read: rendered PDF131, printed p118. G4 is explicitly sibling pairs in `F1^e` (the extracted p121–122 heading's F2 is not a reliable replacement). Figure 6.6 fixes the original pair `(a,c)`, uncle d with possible children `(u,v)`, and e with possible pairs `(a',c'),(u',v')`. The induction is backward over groups and smaller budget only for empty credits. G1 resets A/B and credits C; A2BC gives Q empty, A3BC gives Q=P. G2 first contracts a common `(u,v)` if present; unary branches reset.

Source ledger entry 5 — read: printed pp123–126 / PDF136–139. G4 union rule adds the incoming P'/Q' to local G1–G3 assignments, except A3BC at G4.1 resets B and 2B always resets. Thus a literal nested union has no automatic two-credit cap. G5 uses P={a} or {a,a'} and requires non-sibling geometry; two credits either yield no children or one pendant branch of cost at least two. G6 explicitly releases only empty-credit states to smaller-budget induction. A count inequality alone cannot validate any of those reachability/import requirements.

Source ledger entry 6 — read: printed pp103–104 / PDF116–117. Active Rt nodes represent entire common subtrees; singleton root removal removes the matching component from active T1 and moves it to Rd. This review treats a common-subtree merge as a new active cluster name, preserving any protection on the remaining attachment edge. Calibration file `../controls-frozen.json` was opened only after source reconstruction. Its five families are exposed, inherited fixtures; they cannot certify universal claims. Before execution, expected exact outcomes are frozen there and will be checked through fresh code with deliberately corrupted twins.

Control lineage entry 1 — read: `results/thesis-complexity-reachable-trace.json`. Explicit nine-leaf trees and branch sequence C(a,c), A(d,a), then oriented pair (y,x) supplied as calibration data. The receipt calls itself a structural trace, not a runtime counterexample. Fresh code will reconstruct its states from initial trees rather than trust intermediate serializations.

Control lineage entry 2 — read: `results/thesis-complexity-three-credit-trace.json`. Explicit thirteen-leaf initial trees and C,A,C,C branch sequence supplied. The incoming G4.1 has four pendants, so this fixture is a reachable three-credit calibration, not a three-pendant target witness. I will calculate credits by the p123 union/reset rules, independently from the fixture's claimed cardinalities.

## Executed calibration checkpoint (before candidate reading)

Fresh checker: `fresh_checker.py`, standard-library-only, newly authored from original source and explicit fixture data. No source from any prior checker was read or imported. It reconstructs protected vertices, simultaneous cuts and suppression, eligible depth-ranked sibling pairs, ordered endpoints, source-priority cases, common merges, and root removals. A first path-resolution failure was preserved as `fresh_checker.failed-path.py`; it is not accepted evidence.

Executed with `./bootloops-python research/rmaf/thesis_complexity/repair/fresh_review/fresh_checker.py`. Verbatim summary:

```
{"status": "checked", "scope": "exposed finite calibration, not a universal theorem", "elapsed_seconds": 0.010816208001415362}
records 37
```

The 37 records include the intentionally failing corrupted mass assertion, caught by the outer negative-control expectation. The production positive controls pass, the corruption is rejected, and the reverse orientation twin passes. Nine-leaf mass 9/16 exceeds 1/2 by 1/16; its C child has zero legal branches. Thirteen-leaf source-legal C,A,C,C yields |P|=3,|Q|=2 without imposing a cap. The local live C child has three pendants and B only. Wrong orientation generates a one-pendant path only if orientation checking is explicitly bypassed. These are finite exposed calibrations, not held-out verification. No search widening is presently needed; any later enumeration will receive a separate measured pilot and limit.

Candidate read 1 — adversary `PROOF-ATTEMPT.md`. Grade: ordinary local two-active-leaf argument plus conditional recurrence; finite census is unrerun screening, not verification. The argument explicitly requires active a with a protected surviving sibling and orientation. Its arbitrary simultaneous-cut erasure warning is material: physical protection alone does not imply retained active sibling. Its prescribed-cut-shape reasoning is not yet a formal state invariant. The present review has independently reproduced the exposed two-active-leaf tests, but has not used or inspected the adversary implementation. The K-4 live continuation budget and negative-child split require separate allowance composition.

Candidate read 2 — geometry `PROOF.md`. Grade: conditional ordinary three/four-active-root proof argument with local Lean kernels; expressly not a universal source-state theorem. Its strongest extra premise is outside-b history H2; the A/B allowances and empty-credit frontier estimates remain imports. Lemma 1's no-sibling-cuts property excludes the arbitrary-deletion erasure control. Lemma 5's no-free-B-merger and two-protected pendant distance are attack sites. Its frontier reset is a proposed annotation amendment, not the original union map. No geometry implementation has been read or imported.

Candidate read 3 — geometry `REVIEW-NOTES.md`. The author records that illegal B cannot support the stronger C distance claim and corrected the proof to use two endpoint estimates instead. This is a hypothesis correction, not an executed reachable counterexample. Fresh review must retain that legal-B premise in all distance checks. The finite search counts remain author-side sampling evidence until replayed independently.

Candidate read 4 — recurrence `report.md`. Grade: conditional recurrence theorem and finite abstract transition arithmetic. It claims only conditional closure and identifies the necessary weaker C bound `alpha*2^(K-3)+2`. Its 37 table rows do not imply source-state transition coverage; p=3 includes but does not solve all histories. The A credited continuation is explicitly open, and the outer induction cannot supply it automatically. Fresh exact composition and source-to-table scope remain to be checked.

Candidate read 5 — recurrence `state-invariant.md`. The proposed weight is multiplicative `2^-(p-q)*(3/4)^q`, with intercept p-3. Its three-credit discharge is a specific legal cost-two row, not closure of every p=3 state. The weaker C interface is exact relative to saturated A/B allowances. Finite prefix counts use expanded calls V, exclude frontier calls from V, and count trivial reductions at zero. Arbitrary negative budgets are explicitly terminal; formula evaluation is restricted to the clipped boundary range. All these distinctions will be retained in the interface ruling.

Candidate read 6 — recurrence `RepairArithmetic.lean`. It imports Std only. Integer-scaled inequalities preserve the claimed A/B/C offsets, and the frontier theorem requires both pointwise exit allowances and its aggregate test. The finite `good` predicate uses truncated natural `4-cost`, so its interpretation is limited to declared capped costs <=4; no theorem here validates arbitrary actual cost input. Every source-facing assumption is exposed rather than derived. Compilation and printed axiom checks are pending.

Candidate read 7 — geometry `Geometry.lean`. Std-only conditional survival theorem proves survival from the recursively global no-sibling-cuts hypothesis, without encoding source cut sets. Other lemmas are path-number constraints and affine integer arithmetic. The negative cherry erasure is a theorem proving the expected false survival result, not a failed compilation. Small-budget ternary values are explicit finite arithmetic. No source-state universality is present in this file.

## Clean formal-kernel compilation

All final candidate Lean modules were copied verbatim into this review's directory with extra `#print axioms` commands for every theorem. `./bootloops-lean` compiled geometry (0.4545 s), recurrence (0.5266 s), and adversary (0.4234 s) with exit zero. Declaration scans excluded `sorry`, custom axioms, `admit`, and `native_decide` after removing comments. All printed dependencies are empty or subsets of the standard `propext`, `Classical.choice`, `Quot.sound`. Full source hashes, logs and theorem lists are retained in `lean-compile-receipt.json`. This accepts their stated conditional formal kernels only.

## Finite attack plan, measured before widening

The first 400 lexicographically generated local trees produced just one target orientation; that pilot is retained but is unsuitable for a representative projection. A fixed-seed shuffled pilot of 600 local trees produced 24 admissible outside-b orientations, 192 budget tests and 350 source-cut-shape checks in 0.252422375 s, with no fire. The same checker will next enumerate all 945 six-label and 10395 seven-label connected rooted binary F2 trees against fixed three/four-root F1 fringes, with K=0..7. Linear input-count projection is 4.77 s; unequal case costs remain an explicit uncertainty. A 60 s timeout bounds this finite widening. Progress units are independently evaluated target orientations and their frontier certificates. The local states have no claimed unprotected-root source histories; they test conditional geometry only.

## Newly checked source identity ambiguity

Rendered PDF132 / printed p119 confirms the prose assigns `P=P' union {u}` and `Q=Q' union {v}` in the A3BC C child, but the displayed recurrence on the same page assigns `Q union {u}`. The cut node is v. The former need not satisfy the p117 declaration Q subset P; the latter does. The frozen three-credit fixture and this fresh replay use the displayed `{u}` assignment. Thus its physical source-legal branch history and |P|=3 are independently reproduced; exact Q={x,u} identity is conditional on the displayed-equation convention, not an entirely literal reading of both conflicting sentences. This is a source inconsistency, not permission to modify frozen records. No runtime conclusion depends on silently resolving it.

## Executed candidate-copy mutation and finite geometry attack

The copied adversary argument with its orientation premise deleted fails at the explicit local fixture: C's sole legal branch cuts one edge, against the claimed minimum three (LHS=1, RHS=3, residual=-2). The reverse twin passes. A copy of the geometry Lean file with `hy<=hx` weakened to True was rejected by Lean. Both failing copies and their logs are retained. This is a deliberate out-of-source mutation, not a source-reachable runtime counterexample.

The widened fresh attack finished in 7.636447125 s: 11,340 connected local F2 trees, 708 admissible orientations, 5,664 frontier-budget tests for K=0..7, and 7,274 legal source-cut-shape checks. No fire. These local tests enforce the outside-b hypothesis; they do not prove it from source history, do not enumerate all forests, and do not establish an infinite state theorem. The 708 examples are distinct tested tree/orientation states, not independent biological/statistical samples.

## Exact interface and additional controls

`interface_audit.py` completed with 77 source/abstract rows, 35/37 passing multiplicative schemas, 16 A/B/C compositions and 40 finite negative-boundary states. The two multiplicative exceptions are preserved. `additional_controls.py` completed 22 post-candidate targeted controls, including every protection/branch snapshot in both exposed physical traces, root-sibling refusal, arbitrary-double-cut failure and its single-cut twin, and a real C,A,B budget sequence 2,1,0,-4. Generic-A allowance substitution fails as an abstract inference at X=128: LHS 93, RHS 62, residual 31. Machine-readable instance and scope are retained.

## Final review grade

Conditional formal kernels and finite checks are accepted at the scopes specified in `RULING.md`. No unconditional source-runtime theorem is accepted or rejected. The next small source lemma concerns active-a survival, protected-sibling retention and outside-b placement for each source-reachable three/four-root J. Even that lemma leaves the credited A allowance and the repaired frontier interpretation to establish. Every source-facing import has a downgrade to conditional/open rather than a silent assumption.

Acceptance/prose checks: exact arithmetic needs no floating-point precision ladder or fitted-constant recognition. The exposed calibration set remains exposed. The final report was checked once for provenance, numbers and scope, then again for source locators, clear subjects and repeated qualification. The second pass corrected the finite-search tie-policy scope and distinguished the p119 displayed-Q convention from its conflicting prose. These are author-side edits to this review; the coordinator remains responsible for reviewing its final text. No new external scientific claim or bibliography entry is made.
