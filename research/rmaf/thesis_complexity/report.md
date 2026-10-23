# Whidden Chapter 6 complexity: local proof obligations

The O(2^q n) claim remains open in this reconstruction. Exact arithmetic and two reachable tree traces identify omissions in the analysis on printed pages 117–123. Neither trace establishes a larger asymptotic running time. In the first trace, a child terminates immediately and a tighter bound covers the apparent excess. A fresh reviewer must check the source-to-model translation before these findings are treated as independently confirmed.

## Source and convention

The source is Chris Whidden, *Efficient Computation and Application of Maximum Agreement Forests*, Dalhousie University, July 2013. I read Chapter 2 definitions and all of Chapter 6, including the missing extracted pages by inspecting PDF images. Printed page p corresponds to PDF page p+13. Theorem 6.13 begins on printed page 116 and ends on page 126. The relevant algorithm is Figure 6.5 on page 111; the depth rule is on pages 110–111. The local PDF SHA256 is `0dd9ced63f26ab608dc484cfe853d52171565b0cc704bb61336dd64a15c2bbe9`.

Here q denotes remaining cuts, including the thesis's labelled unary rho root. The thesis writes k for that budget and q for the number of pendant nodes. I write s for pendant count, p=|P|, and r=|Q|. Conversion to unaugmented rooted MAF belongs to the separate convention review.

The quoted source sentence on printed p117 is: “P is a set of up to two nodes whose parent edges are protected in F1; Q is a subset of P.” The source's proposed descendant-count bound is

    B(K,p,r) = alpha * 2^K * (2+r)/2^(p+1) + p - 3.

The displayed bound and the exceptional assignments on p123 were checked against the PDF. All source assertions are distinguished from the computations below in `source-notes.md` and `transition-ledger.md`.

## Exceptional recurrence

On printed p123, a G4.1 A3BC invocation passes unchanged P,Q to its A-child, resets P=Q=empty in its B-child, and adds the newly protected endpoint to both P and Q in its C-child. At p=1,r=0,s=3, substituting the source's child bounds gives normalized coefficient

    1/4 + 1/8 + 3/16 = 9/16 > 1/2.

Including the additive offsets, set X=alpha*2^K/16. The parent bound is 8X-2; the substituted child sum, including the current invocation, is 9X-5. Their difference is X-3. At X=4, these bounds are 30 and 31. Lean proves the universal affine identity and failure for X≥4. This calculation concerns the bound substitution; it does not count actual descendants.

The condition is specific: the normalized inequality is `9+3r ≤ 8+4r`, equivalent to `r≥1`. Thus r=1 passes, and s≥4 also avoids the excess. The missing case is r=0,s=3.

A nine-leaf example reaches that case in the full legal recursive-call tree used for the running-time upper bound. The replay uses an initial cut budget of at least two and does not model optional early-success short-circuit evaluation. In the following Newick expressions, the outer unary node is labelled rho:

    F1 = (((((a,c),d),(x,y)),((z,w),(t,h))))rho
    F2 = ((((a,((x,z),(d,((y,w),t)))),h),c))rho

The chosen sibling pairs, oriented by F2 depth, are (a,c), (d,a), and (y,x). The corresponding cases are A2BC, A2BC, and A3BC. Choose the first C-child, cutting c and protecting a and the two pendant edges. Next choose the A-child of the protected-ec A2BC, cutting d and protecting its two pendant edges. The G4 pair (y,x) then has exactly three pendant nodes w,t,z. All three candidate branches are legal, all earlier cases fail, and the analysis input is P={a},Q=empty.

`reachable_trace.py` checks the trace, and `Trace.lean` separately evaluates its trees, cuts, protection transport, depth choices, earlier-case predicates, and candidate cut legality. Both programs were written in this arm from the same source reading, so their agreement does not constitute fresh-author verification.

The same Lean file follows this example's C-child. It has both endpoints protected and a protected pendant edge, so it makes no further recursive calls. This explains why the local substitution failure cannot be promoted to a runtime counterexample.

## Credit cardinality

The union instruction on p123 can produce p=3. A second trace starts with 13 leaves, applies A2BC twice, then reaches three-way A3BC invocations in G4.1 and G4.2. Taking their C-children creates P={a,x,u},Q={x,u}. The exact trees, predicates, and cuts are in `../results/thesis-complexity-three-credit-trace.json`; the `ThesisTrace.More` namespace checks the same finite trace in Lean.

The normalized branching arithmetic can accommodate some p=3 states. This finding requires the proof to extend its state domain or change its assignment rule. It does not show that the base 2 bound is impossible. The original arithmetic receipt includes unrestricted union variants as diagnostic rows; only the specific A3BC trace just described has been shown reachable here.

A separate transcription issue occurs on p119: the prose inserts v into Q while the displayed recurrence inserts u. Since the new protected endpoint and member of P is u, the literal prose violates Q⊆P. This arm used the displayed recurrence for its numerical check and retains the discrepancy for source review.

## Smallest remaining obligation

For every reachable G4.1 invocation J with P={a},Q=empty and exactly three pendant nodes, under the induction bounds already established for smaller uncredited invocations and subsequent groups, prove

    1 + I(J_A) + I(J_B) + I(J_C) ≤ B(K,1,0).

The three individual source bounds do not imply this inequality. A sufficient candidate repair is the strengthened C-child bound

    I(J_C) ≤ alpha * 2^(K-3) - 1,

instead of the assigned `3*alpha*2^(K-4)-1`. The A and B bounds would then yield `alpha*2^(K-1)-5`, below the parent allowance. This strengthened bound remains unproved in general. For a G4 subtree containing only the processed sibling pair, the source's own G5 double-protection calculation already supplies a stronger C-child estimate. Subtrees with three or four active leaves require the remaining structural analysis; the demonstrated p=3 state must be included when four leaves survive.

The next experiment should enumerate these remaining G4 configurations with explicit protected-edge locations and depth ordering, retaining the original ancestor A2BC history. It must evaluate the combined descendants or prove a stronger C-child invariant. Permitting arbitrary transitions between (p,r) counts would discard the restrictions that the source uses and would not answer this question.

## Verification and limits

The Fraction audit executed 44 diagnostic transition rows after nine frozen hand controls. The controls include exact nulls, a false recurrence, a false credit reset, and invalid credit-cardinality/subset states. A second four-case structural control record was written before the structural-checker code but after the candidate tree had been reasoned about; it is diagnostic evidence and was not held out from discovery. Both Python runs retain JSON and logs. The recorded calculation times were below one hundredth of a second; those values exclude launcher startup.

`Credit.lean` and `Trace.lean` compile with Lean 4.35.0 through `./bootloops-lean`. The final axiom prints contain only propext, Classical.choice, and Quot.sound; several statements are axiom-free. No sorry, custom axioms, or native_decide appear in the accepted source. A deliberately false `9≤8` file was rejected by Lean. Two failed edit/compile logs are retained as repair history and are excluded from accepted evidence.

The source asserts O(n) work per invocation by adapting previous arguments. This arm has not proved that data-structure bound. Recomputing tree information after every trivial reduction gives an explicit polynomial O(n³) local upper bound; each reduction decreases the number of active roots, and every recursive edge consumes at least one cut. Thus the recursion depth is at most q0+1 from initial nonnegative budget q0. A corrected exponential argument would still need the local O(n) implementation to recover the exact theorem statement. Producing the cut witness requires only polynomial additional replay work. At the optimum in the rho convention, qopt=m_rho-1, so 2^qopt=2^(m_rho-1); a decision budget q0 allows at most q0+1 components. The unaugmented parameter transfer remains separate.

The scientific status is open. No novelty claim, acceptance of Theorem 6.13, or rejection of its asymptotic claim follows from this report. Fresh semantic review and the strengthened structural estimate remain necessary.
