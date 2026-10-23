# Recurrence route: conditional repair

The joint G4.1 runtime bound remains open for the source algorithm. This route gives a kernel-checked conditional composition, a finite credit table that includes the recorded three-credit state, and a precise continuation certificate that would complete the use site. No geometric lemma or universal protection-persistence claim is imported.

The C-child estimate needed after the source A/B allowances is weaker than the proposed repair target:

`I(C) ≤ alpha*2^(K-3)+2`

already implies

`1+I(A)+I(B)+I(C) ≤ alpha*2^(K-1)-2`.

The sufficient estimate with additive -1 is therefore three invocations stronger than necessary. The exact interface and its full frontier composition are proved in `RepairArithmetic.lean`.

The proposed ordinary-state coefficient is `(1/2)^(p-q)*(3/4)^q`, with additive term `p-3` and all ten states `0≤q≤p≤3`. Exact checks of 37 enumerated transition schemas find 35 passing rows and two exceptional G4.1 three-pendant reset rows. The recorded `(3,2)` state discharges legally through a cost-two B branch in the frozen thirteen-leaf example. The original additive coefficient formula has an additional abstract lifted-discharge obstruction at `(2,2)`; that row's source reachability has not been established.

A finite prefix certificate expands actual legal branches until terminal calls or empty-credit induction boundaries. If the C prefix has V expanded invocations, L exits and exit decreases d, its majorant is

`alpha*2^(K-1)*sum(2^-d) + V-3L`.

The conditions `sum(2^-d)≤1/4` and `V-3L≤2` suffice. The Lean theorem accepts the exact aggregate allowance inequality, so a certificate can use sharper intercept slack. Common sibling merges and F2-root removals add zero invocations within that prefix. A branch that overshoots the negative-budget range is a terminal call and is handled directly.

## Executed evidence

- 31 named controls passed in `thesis-runtime-repair-recurrence-final.json`: the nine-leaf overshoot/dead C, thirteen-leaf three-credit assignment and B-only continuation, live two-active-leaf case, wrong-orientation mutation and positive twin, arithmetic plants, unary-rho preservation, inherited protection, protected-cut refusal, and root-sibling restriction. The negative-budget assertion loop also checked all 40 boundary states.
- The multiplicative table has 35 passing rows and two explicitly retained exceptional rows. This is finite arithmetic evidence and makes no universal source-coverage claim.
- The state-coverage adversary rejects three hypothetical transitions. None is asserted source-reachable. It demonstrates why merely enlarging the credit domain cannot prove the algorithm bound.
- Lean compiled the positive file successfully. The conditional frontier theorem uses only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`; the finite row and boundary theorems have no axioms. No custom axioms, admitted terms, or `native_decide` are used.
- Lean rejected the intentional false inequality in `NegativeControl.lean`. The first compilation failure, caused by an unavailable list relation, is preserved in `lean-v1.log`; the corrected relation is defined in the proof file.

## Import ledger

| Item | Use | Status |
|---|---|---|
| Local thesis Ch2 and Ch6 pp104–111,117–126 | Definitions, exact cuts, rule order, credit assignments | Read from text; omitted extraction pages 110/118 rendered and inspected |
| Parent REPAIR-TARGET and frozen control JSON | Scope and expected controls | Read before construction |
| Original nine- and thirteen-leaf JSON traces | Development controls | Read; fresh local control code, no original implementation imports |
| Empty-credit smaller-budget induction hypothesis | Frontier exits | Explicit conditional hypothesis, subject to terminal-budget checks |
| A nonempty-credit allowance | Main use site | Explicit conditional continuation premise; not granted by the outer induction |
| Two-active-leaf geometric lemma | None | Not assumed; remains open in this route |
| Geometric arm, adversary proof/code, parent implementations, correctness/transfer work | None | Not read or imported |
| Source-wide transition coverage, bounded local rank, treatment of every p=3 history | Needed for algorithm application | Open |
| Fresh nonauthor verification and referee simulation | Required for acceptance | Deferred to parent; this author cannot supply independence |

## Remaining structural premise

For each source-reachable G4.1 state with P={a}, Q empty and three pendants, construct the exact C continuation prefix and establish its frontier allowance test. Every step must respect ordered case priority, correct orientation, root restrictions, simultaneous source cut sets, protection inheritance, and within-invocation normalization. The A continuation and all nonempty-credit exits require their own valid certificates. A proof of these premises would make the formal composition applicable; the current finite controls do not establish them.

The result is a conditional recurrence theorem awaiting structural proof and fresh verification. The aggregate theorem count is unchanged.
