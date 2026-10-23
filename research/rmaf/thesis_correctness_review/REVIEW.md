# Independent correctness review

The reconstruction remains **OPEN** for universal correctness. Its seven local Lean theorems compile with the reported standard axioms, and its decisions agree with a fresh exact reference on 534 tested pairs and 2,507 budgets. The review found two concrete problems in the proposed mathematical interfaces: universal coverage of raw optimal cutsets is false, and the standalone normalization lemma needs an active-state compatibility hypothesis in addition to a root-safe formula. Neither finding is a wrong decision by the algorithm.

The reviewer read the campaign specification and primary thesis before opening the reconstruction. The frozen controls, independent graph implementation, pilot results and first cut/partition census precede access to `SEMANTICS.md`, `ProtectedBranch.lean`, `algorithm.py` or `reference.py`. The original files and results were preserved. No complexity or transfer agent's work was read.

## Raw optimum coverage

`ProtectedBranch.lean` defines `Cover` at line 15 by quantifying over every cutset satisfying `Optimal`. Its two A2BC theorems consume this premise at lines 30 and 52. When `Optimal` means all minimum original-edge cutsets, this premise is false even at an initial A2BC state.

Use labelled unary rho roots and the trees

```
T1 = rho → (a,(b,(c,d)))
T2 = rho → (((a,c),b),d).
```

The selected T1 cherry is `(c,d)`, and its T2 pendant subtrees are `a,b`. The optimum is two cuts. Cut the incoming edge of the T2 cluster `{a,c}` and the incoming edge of leaf `a`. The resulting agreement forest has label blocks `{a}`, `{c}`, `{rho,b,d}`. This cutset contains neither endpoint edge, and it contains only one pendant edge. Thus `A ∨ BB ∨ C` is false on this optimum. Independent edge deletion and partition enumeration establish the optimum and forest validity in [cover-adversary.json](cover-adversary.json). The bounded search found this failure in 36 tree/cherry states; the later actual-state audit found 21 violating optimal cutsets among its sampled states.

Whidden's Lemma 6.8, printed p.105 (PDF p.118), asserts that at least one listed branch decreases the remaining optimum by its cut count. That is an existence statement. Equivalent edge cuts can yield the same forest, so existence does not imply universal membership of a specific original edge. The compiled conditional theorems are sound, but the source lemma cannot supply their `Cover` hypothesis for all raw optimum cutsets.

[ExistentialRepair.lean](lean-isolated/ExistentialRepair.lean) gives a narrower formal interface. Existence of a covered optimum, together with failure of the earlier branches, supplies an optimum in the selected child. For every optimum containing that child's cut edge, the pendant-exchange premise excludes the newly protected pendant edges. Three lemmas formalize this logic with no axioms. The symmetric protected-c case follows by swapping the endpoints. These lemmas still require graph coverage, exchange and transport proofs. The BCY theorem also assumes universal per-cutset coverage; its source Lemma 6.11 supplies existential branch coverage. The sampled BCY states did not refute its stronger premise, so that specific premise remains unverified rather than refuted.

## Normalization domain

The reconstruction correctly identifies a root-parent omission in Lemma 6.5, printed pp.101–103 (PDF pp.114–116). The review independently reproduced its three-leaf root example and a separate four-leaf fixture. Deleting the selected path edges preserves an AF in both fixtures when the LCA has no parent. These finite checks do not prove the general root case.

A second witness shows that root handling alone does not repair the lemma on its literal standalone domain. Let

```
T1 = rho → ((a,b),(c,d))
T2 = F2 = rho → ((a,c),(b,d))
F1 = {(a,c), b, d, rho}.
```

`F1` is a forest of `T1`. Take `E={ea,ec}` and `E2=∅`. The pair `(a,c)` is a sibling pair in both `F1` and `F2÷E2`, and `F2÷E` is the AF with blocks `{a}`, `{c}`, `{rho,b,d}`. Both path edges are cut. Their LCA has a parent, so the stated normalization replaces them by the incoming LCA edge. The new blocks `{a,c}` and `{rho,b,d}` overlap in `T1`; normalization fails. [normalization-domain.json](normalization-domain.json) retains the exact graph, overlap vertices and a passing twin with `T1=T2`.

This witness violates the algorithm's component-containment invariant: the connected `F2` is not contained within a single component of `F1`. Chapter 2, printed p.17 (PDF p.30), explicitly says intermediate algorithm states maintain that invariant and gives Lemma 2.2 to identify their AFs with AFs of the original trees. `SEMANTICS.md` already lists the intended invariant. Consequently this witness does not refute normalization on valid active states. A repaired theorem must carry that invariant, or an equivalent AF compatibility premise, into the proof; root-parent existence is insufficient by itself.

## Source use sites

The primary-source text and the rendered printed p.110 were inspected directly. The thesis adds a labelled unary root rho on printed p.12 (PDF p.25); all candidate comparisons use that convention. No conversion to the campaign's unaugmented convention was inferred.

| Source or interface | Actual consumer | Ruling |
|---|---|---|
| Lemma 6.3, p.101 | Proof of 6.4, p.101; proof of 6.5, p.102 | The general statement omits component containment from Lemma 2.4, p.18. An exact two-label witness reproduces that omission. These two proofs compare against connected original T1, where containment is automatic. |
| Lemma 6.5, pp.101–103 | First exchange in 6.10, pp.112–113 | The A/C path LCA has sibling x and therefore a parent. AF compatibility with the active F1 must be carried explicitly. This source-domain repair does not change the intended active-state branch. |
| Lemma 6.5, p.113 | Second exchange in 6.10, pair `(x,u)` | The parent of the pair's LCA must exist, or the root-safe case must be proved. No such root case occurred in the 120 sampled snapshots; the source invocation alone does not establish its domain. |
| Lemmas 6.4–6.5, p.116 | A2BC protection exchange in 6.12 | Preserve pendant cuts, remove path cuts, and restore at most one available parent edge. The cardinality inequality is checked in Lean; AF preservation and edge provenance remain graph obligations. The protected-c form needs the swapped endpoint argument. |
| Lemmas 6.6–6.11, pp.105,112–114 | Local branch coverage in 6.12 | Their stated optimum-decrease alternatives supply existential optimal branches. They cannot be silently strengthened to universal raw-cutset coverage. Chapter 3 proofs remain conditional source imports in this review. |
| Theorem 6.12, pp.114–116 | Final decision correctness | Markings affect depth eligibility, BCY applicability and the protected-c A2BC order. A marked-state induction or an explicit coupling is required to justify the comparison tree. The missing coupling is an obligation, not an algorithm counterexample. |
| OR inheritance, p.107 | Protection after suppression | `Forest.reduce` implements OR, and `legal` excludes a cut whose root sibling is protected. The two Boolean Lean theorems prove their stated list properties. Lifting optimal cutsets through graph suppression remains open. |
| Rt contraction and completion, pp.104,111 | Success and recursive states | Common cherries contract before root completion, as Figure 6.5 specifies. `merge` removes protection internal to the new atom. A universal proof must justify common-subtree preservation and expansion of successful states. |
| Depth rule, p.110; endpoint order, pp.23–24 and p.121 | Pair selection and special cases | The code follows protected-top eligibility, maximum F1 depth and F2 tie priorities. A is at least as deep as C. Replacing a common pendant subtree by an atom leaves the depth of that subtree's root unchanged. Preservation of the marked-path invariant remains a graph proof obligation. |

The executable branch table agrees with the source's priority AC, B, RB, RB*, 2B, BCY, A2BC, A3BC, including B-before-A when c is protected. Figure 6.5's SC/AC naming inconsistency does not create a new case. No branch table error was found in the inspected code. Unexpected shapes remain explicit `SemanticHole` failures.

## Executed evidence

| Check | Result | Scope |
|---|---|---|
| Frozen exact controls | 14 controls passed; expected-answer, overlap and inheritance corruptions detected | Written before author files were opened |
| Independent cuts versus partitions | 468 ordered pairs; zero disagreements | All three- and four-leaf pairs, with and without labelled rho |
| Independent two-pendant exchange | 288 nonvacuous cutset/endpoint premises passed | Same finite tree census |
| Candidate versus fresh partition reference | 534 pairs; 2,507 budgets; zero disagreements | All 225 four-leaf pairs, 150 sampled five-leaf pairs, 150 sampled six-leaf pairs, nine author-selected branch witnesses |
| Branch reach | All nine branch variants reached | Includes protected-c A2BC and BCY |
| Actual candidate snapshots | 120 states; 50 normalization constructions passed | Zero sampled root-normalization premises; four omitted-removal corruptions caught by a retrospective control |
| Original Lean statements | Seven compiled | Only `propext` and `Quot.sound`; the four branch-logic theorems use no axioms |
| Lean controls | True twin passed; false twin rejected | Rejection explicitly says the arithmetic proposition is false |
| Existential interface repair | Three compiled lemmas | No axioms; AF premises remain assumptions |
| Original reported census | 14,250-pair receipts and all source hashes agree | Inspected records; this full census was not independently rerun |

[thesis-correctness-review-summary.json](../results/thesis-correctness-review-summary.json) records the counts, hashes, proof commands and findings. Pilot timings justified each bounded extension; the largest final state audit took less than one second. [WORKFILE.md](WORKFILE.md) records chronology, including a reviewer set-mutability bug corrected before the state audit produced evidence.

Universal correctness still requires source structural coverage, root-safe AF normalization on valid states, original-edge transport, common-subtree contraction, finishing, termination and the global marked-state induction. Complexity, convention transfer and novelty were outside this review.
