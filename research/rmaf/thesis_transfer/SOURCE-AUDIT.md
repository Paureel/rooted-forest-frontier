# Whidden source reconstruction checkpoint

The thesis states an augmented rooted-SPR decision algorithm taking O(2^q n) time. The convention-transfer note supplies a provisional exact reduction from ordinary no-rho MAF to that problem. The thesis algorithm itself remains unverified in this campaign. The source contains a substantial correctness and running-time argument; lack of a later journal proof would not refute it.

## Source and reading ledger

Primary source: Chris Whidden, *Efficient Computation and Application of Maximum Agreement Forests*, Dalhousie University PhD thesis, July 2013. The official institutional PDF was opened at https://dalspace.library.dal.ca/bitstreams/3b246ff4-5ec2-452f-95ab-ef1aed255373/download, and its title page was checked against the local copy. Local PDF has 214 pages. Printed page p is PDF page p+13 in the chapters used here. Hashes are in source-ledger.json.

Read this session: Chapter 2 printed pp12–18; Chapter 6 printed pp100–127; Chapter 3 printed pp21–28 from Lemma 3.3 through the end of Lemma 3.8; the named references on printed pp183/190. PDF pp121,123,131 are extraction gaps: existing rendered images were inspected for the branch diagrams, depth rule, G1/G2 analysis, and Figure 6.6. PDF p114 was newly rendered to verify Lemma 6.3's literal statement. PDF pp128–129 were rendered to verify the protected-edge proof across printed pp115–116.

Unopened primary imports: the external full texts cited as [22], [23], [101], [102]. Their names and reference numbers below identify imports as listed in the thesis; bibliographic metadata beyond the thesis itself has not been independently verified and no new bibliography entry is added. The theorem in [23] is used as a retrieved statement through the thesis, not as an independently checked source proof.

## Retrieved statements

| Item | Exact locator | Source assertion and use |
|---|---|---|
| Root augmentation | printed p12 / PDF25 | Adds labelled rho above the original root, “whose only child is the original root”; rho is included in X. |
| AF and distance | printed p15 / PDF28 | AF means a forest of both inputs; minimum component count m; additional cut optimum e; rooted SPR distance = e(T1,T2,T2)=m(T1,T2)−1, attributed to [23]. |
| Ordinary versus acyclic | printed pp14–15 / PDF27–28 | MAAF has a separate acyclicity condition; Figure 2.2 includes a cyclic MAF. Chapter 6 concerns ordinary MAF/SPR. |
| Decision claim | Theorem 6.1, printed p100 / PDF113 | O(2^q n) decision for rooted binary trees and cut/distance budget q. Corollary 6.2 iterates the decision algorithm to find the optimum. |
| Correctness | Theorem 6.12, printed pp114–116 / PDF127–129 | Top-level invocation m(T1,T2,q) returns true exactly when e(T1,T2,T2)≤q. |
| Cost | Theorem 6.13, printed pp116–126 / PDF129–139 | O(2^q n), proved through a potential indexed by the cut budget and protected-node sets P,Q. |

These are retrieved claims with their source's strength. They are neither independently verified theorems of this campaign nor discredited merely because some proof details remain to be reconstructed.

## Dependency trace

| Consumer | Essential dependency | Exact hypotheses to preserve | Current ruling |
|---|---|---|---|
| Forest-state equivalence | Lemma 2.2, p17 | F1 partitions into trees, F2 into matching-label forests | Must be retained for all reachable states; not arbitrary unrelated F1,F2. |
| Branch exchange and restrictions | Lemma 2.1, p16, from [22]; Lemma 2.4, p18, adapted from [22] | Empty-component edge shift; component containment, nonoverlap, triple compatibility | External source proof not opened; thesis statements read. |
| AC/B/ABC | Lemmas 6.6–6.8, p105; Chapter 3 Lemmas 3.5–3.8, pp24–28 | Nontrivial sibling pair, common subtrees represented by endpoint nodes, connectivity/pendant count | Chapter 3 proofs read. Suppressed-edge maps and all inherited forest invariants must be made explicit in a reconstruction. |
| RB | p112 | Reversal of the one-pendant rule, preserving forest-state hypotheses | Exact symmetry must be established for the asymmetric maintained state. |
| RB* | Lemma 6.9, p112 | Pendant nodes exist in F1 with the stated chain structure | Reduced in source to Lemma 6.7 on a different sibling pair. |
| 2B | Lemma 6.10, pp112–113 | Two pendants and common uncle with identical subtree | Uses6.4/6.5 twice; exact cut provenance and cardinalities still require replay. |
| BCY | Lemma 6.11, pp113–114 | Protected common uncle is child of the specified pendant node | Underlying three alternatives include cutting protected ex; global protection proof must justify omission. |
| Protection completeness | Theorem 6.12, pp115–116 | Leftmost promising branch, protection inheritance through suppression, root-sibling equivalence | Central remaining correctness obligation. Local cut-optimality must lift through later suppressions to the earlier edge that introduced protection. |
| Base2 bound | Theorem 6.13, pp117–126 | Depth-rule eligibility, P/Q invariants, group order G1–G6, special cases given priority | Central remaining cost obligation. Arithmetic alone does not prove that actual recursion calls have the credited states. |
| Per-node linear work | p116; Chapter 3 Lemma 3.3 pp21–22 | Forest pointers and sibling lists; extension to depth rule and new cases | Chapter 3 proof read; source describes Chapter 6 extension as straightforward. Its implementation and amortization have not been reconstructed. |

The exact potential in Theorem 6.13 p117 is

    alpha * (2^(q−|P|) + |Q| * 2^(q−|P|−1)) + |P| − 3.

The unmarked state P=Q=empty gives alpha*2^q−3. Page118's G1 assigns one protected-node credit to the C branch. G2/G3 propagate or release that credit; G4/G5 use the four-leaf uncle subtree and special configurations to release it before G6 returns to the outer induction. Establishing this graph-to-credit correspondence is essential. A numerical check of the displayed recurrences would only check its arithmetic.

## Executed scope counterexample and safe repair

Lemma 6.3 printed p101 states its equivalence for two arbitrary forests with the same label set, omitting component containment from Lemma 2.4. The literal statement is false: take F1={rho}|{a}|{b}, and F2={rho}|(a,b). F2 contains no triple, and its components cannot overlap in F1 because the required paths do not exist. Nevertheless deleting edges and suppressing vertices in F1 cannot connect a and b. Both forests can be obtained from the same rho-augmented cherry by cuts. The exact check and clean twin are retained in results/thesis-transfer-source-scope.json.

Restoring Lemma 2.4's containment condition repairs this specific counterexample. The calls to Lemma 6.3 in Lemmas 6.4 and 6.5 compare with the connected original tree T1, where containment is automatic. Therefore the counterexample does **not** refute Theorem 6.12 or 6.13 and is not being used to reject the thesis algorithm.

## Smallest next protection obligation

Theorem 6.12's first-new-protection discussion on printed p115 lists branches cutting ec and protecting ea (and, for A2BC, the two pendant edges). The algorithm on p107 also has an A2BC branch with ec already protected: it cuts ea and protects the two pendant edges. The written argument should explicitly cover that branch and carry edge identities through subsequent suppression. Its local exchange is plausibly symmetric, but that symmetry has not been proved here and is not substituted for a proof.

A replayable statement to formalize/test next is:

> In any reachable state satisfying the maintained forest invariant, let a,c be its nontrivial sibling pair with two pendant edges b1,b2. Suppose cutting one endpoint e is optimal and the other endpoint is protected. If an optimal descendant completion in that endpoint branch first needs a protected pendant edge, then some earlier pendant-pair branch has an optimal completion with no larger total cut count, with suppression and root-sibling equivalences accounted for.

The stated protection lemma must hold for each protection origin. After that proof, the depth/credit invariant of Theorem 6.13 remains a separate obligation. No exact counterexample to either global theorem has been found in this work, and the global algorithm has not been implemented or tested here.

## Consequence for comparison

The opposite-caterpillar transfer uses valid top-level binary trees, so it avoids extending Theorems 6.12/6.13 to arbitrary externally initialized forests. Conditional on those source theorems and the transfer proof, ordinary no-rho MAF has the reported O(2^K n) bound. Root augmentation alone is therefore not a reason to exclude the thesis from the campaign's comparison. The appropriate unresolved issue is the source algorithm's validity reconstruction, together with full formal verification of the new transfer proof; novelty remains open.
