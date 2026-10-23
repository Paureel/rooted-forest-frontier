# Protected-edge reconstruction: semantics and proof boundary

The source is Chris Whidden's 2013 thesis, *Efficient Computation and Application of Maximum Agreement Forests*. Printed page numbers below equal PDF page numbers minus 13. This note reconstructs Chapter 6 in its own convention. It makes no conversion claim to the campaign's unaugmented convention and no running-time claim.

## Executable state

`algorithm.py` represents a forest as directed child lists, labels and a set of protected incoming edges (identified by bottom vertices). Rho is the labelled root with one child defined on p.12. It is never replaced by an extra ordinary leaf. Active common pendant subtrees are contracted synchronously to atoms carrying their original label sets. The labels of active atoms implement Rt; finished equal components are removed from both active structures (their equality is the required Rd invariant).

The maintained intended invariants, whose graph-level proofs are still open, are:

1. F1 has one active component; F2 has a forest on precisely the same atom labels. Each atom expands to an equal pendant subtree in both original trees. All removed components were equal in both structures.
2. Every active F2 component is contained in the active F1 component; completed components are paired. Thus Lemma 2.2's component-containment premise holds.
3. Every suppressed incoming edge inherits protection by OR over the original edge path. Protection disappearing at an unlabelled root is prevented by refusing a cut whose root sibling edge is protected.
4. Protected F1 edge bottoms are active atoms, and their tops lie on one root-to-leaf path, as required by p.110's depth rule. Unexpected violations raise `SemanticHole`.
5. The budget is q remaining **F2 edge cuts**, not a component count. Synchronous contraction and completing an already separated component cost zero. The negative-budget test precedes success.

At each iteration the selected sibling pair has maximum F1 depth among pairs below the deepest protected-edge top. Ties prefer pairs in different F2 components, then the deeper F2 member; remaining ties are arbitrary. The endpoint named a is chosen at least as deep in F2 as c, as the analysis explicitly assumes on p.121. This endpoint-order convention is used by the source's analysis but is not stated in Figure 6.5 itself. The implementation declares it rather than hiding it.

A common cherry contracts before root-component completion, matching Figure 6.5 steps 4–6. Contracting deletes protected edges internal to the new atom: they cannot subsequently be selected for cutting while the atom remains contracted. This optimization requires the common-subtree preservation lemma in a universal proof; finite comparisons do not supply it.

## Branch table

Let a,c be the selected nontrivial sibling atoms of F1. Let B be the ordered pendant-edge list on the F2 path from a to c, from a toward c. Let x be the sibling of their parent in F1, when it exists. Every proposed cut is refused if it intersects protection or cuts a root edge whose sibling is protected. All listed tests occur in this priority.

| Case | Condition | Ordered cut/protection operations | Source |
|---|---|---|---|
| AC | Different F2 components | Cut a; cut c | p.107 |
| B | One pendant edge | Cut B | p.107 |
| RB | F2 sibling of a (respectively c) equals x | Cut c (respectively a) | p.109 |
| RB* | c is child of LCA; x is the specified caterpillar of all pendant subtrees | Cut a | p.109, Lemma 6.9 p.112 |
| 2B | Two pendants; x equals sibling of F2 LCA | Cut both pendants | p.109, Lemma 6.10 pp.112–113 |
| BCY | x exists in F2, its incoming edge is protected, and x is a child of the first pendant node | Cut B; cut c and x's sibling y | pp.109–110, Lemma 6.11 pp.113–114 |
| A2BC | Two pendants; c unprotected | Cut a; cut B; protect F1 a and F2 a,B, then cut c | p.107 |
| A2BC protected c | Two pendants; c protected | Cut B; protect B, then cut a | p.107 |
| A3BC | At least three pendants | Cut a; cut B; protect a in both forests, then cut c | p.109 |

The pseudocode calls the first case SC (p.111), while the definition calls it AC (p.107); this reconstruction uses AC. No undefined SC rule is invented. Unsupported shapes, absent matching atoms, duplicate cuts, absent parent edges and unavailable eligible sibling pairs raise `SemanticHole`. The `protection=False` option is an experimental unprotected comparison only; it is not claimed to be the identical fixed recursion tree used in the source's proof.

## Source proof dependency and use-site map

| Object | Immediate consumers in the correctness chain | Required interface and current ruling |
|---|---|---|
| Lemma 2.1 (p.16) | Chapter 3 branch lemmas, then 6.6–6.8 | Shift a cut across an empty component, preserving yielded forest. Source import; not formalized here. |
| Lemma 2.2 (p.17) | Active F1/F2 representation, p.103–104; all structural branch lemmas | F2 component labels refine F1 components. Explicit state invariant required; cannot drop it. |
| Lemma 2.4 (p.18) | Lemma 6.3, implicitly | Forest characterization has containment, no overlap, compatible triples. |
| Lemma 6.3 (p.101) | 6.4 and 6.5 | Standalone statement omits containment. At these consumers the comparison is against connected original T1, so containment is automatic. Overstatement does not refute these consumers. |
| Lemma 6.4 (pp.101–102) | 6.10; Theorem 6.12 A2BC exchange | Further cuts preserve AF. Can be derived directly from transitivity of edge-cut refinement; graph proof open. |
| Lemma 6.5 (pp.101–103) | 6.10 twice; Theorem 6.12 A2BC exchange | Once a,c are made siblings by a subset of an AF cutset, remove one path cut for free or replace at least two by the LCA parent edge. Root/LCA-parent existence and original-edge transport must be explicit. |
| Lemma 6.6 (p.105, citing Ch.3) | AC; Theorem 6.12 unprotected coverage | At least one endpoint edge can belong to an optimal completion. Printed `e_b` is inconsistent with the defined AC branches and with the absence of b in this case; implemented cut-c rule is the defined algorithm. |
| Lemma 6.7 (p.105) | B; RB by role exchange p.112; 6.9; 6.10; 6.11 | Unique pendant edge belongs to an optimal completion. The RB role exchange must transport the active-component invariant, not merely rename two arbitrary forests. |
| Lemma 6.8 (p.105) | A2BC/A3BC; 6.10; 6.11; Theorem 6.12 | An optimum contains endpoint a, all pendant edges, or endpoint c. Again printed `e_b` at the final alternative differs from the defined cut-c algorithm. |
| Lemma 6.9 (p.112) | RB* | Its first two pendant nodes form a sibling pair in F1; apply 6.7 with a as unique pendant node. |
| Lemma 6.10 (pp.112–113) | 2B | Exchange a local optimal prefix for both pendant cuts, without increasing total cut count. Cardinality equalities involving chosen prefix E and completion E0 need explicit justification. |
| Lemma 6.11 (pp.113–114) | BCY | Ternary coverage: cut x, all pendants, or c and y. Omission of x is justified only after proving inherited protection excludes every chosen global optimum containing x. |
| Theorem 6.12, soundness (p.114) | Final decision theorem | Each successful terminal state expands to an AF; F2 cut spending bounds component count. Requires contraction/finish invariant. |
| Theorem 6.12, completeness (pp.114–116) | Final decision theorem | Optimal completion exists along a promising path; protection cannot kill it. Requires transport and symmetric A2BC exchange below. |

## The exact remaining protection obligation

For a valid active state, let d be the minimum remaining F2 cuts and let Opt(F) be the d-element original-edge cutsets yielding an AF. Take sibling a,c with exactly two pendant edges b1,b2. For **each** endpoint z in {a,c}, prove:

> If some E in Opt(F) contains z and at least one of b1,b2, then some E' in Opt(F) contains both b1,b2.

The hypothesis is about original edges before suppression, not merely an equal resulting partition. The source derives its cut-c instance using Lemmas 6.4 and 6.5 (p.116). The protected-c algorithm needs the cut-a instance as well. Swapping the endpoint names should supply the structural symmetry, but a formal proof must carry the chosen path and root cases through the swap. `PendantExchange` in `ProtectedBranch.lean` exposes this exact hypothesis.

A second inseparable obligation transports an optimum after cuts/suppression back to an optimum before those cuts: if the residual optimum cuts a protected compressed edge, there is an equal-size predecessor completion cutting an original protected edge in its path; if it cuts the root sibling of such an edge, the two root cuts yield the same forest. This is the graph-level bridge between the proved Boolean OR invariant and the optimum-exclusion argument. Without it, the Boolean proof alone says nothing about AF optima.

These are the smallest **protection-specific** missing obligations. Full algorithm correctness additionally requires the source structural branch lemmas, common-subtree contraction, finishing and termination. They are not all discharged by the six local Lean results.

## A cleaner induction than a fixed unprotected recursion tree

The printed proof says its comparison algorithm introduces no protection (p.114), yet the actual depth rule and BCY applicability depend on protection. Consequently its assertion that adding protection only deletes children needs a coupling argument: different markings can change both the selected sibling pair and selected case. The separate protected-c/cut-a form is also absent from the p.115 introduction-of-protection case list. These observations identify missing formal interfaces; neither is an executed counterexample to the algorithm.

One possible repair, derived here and still conditional, avoids a fixed comparison tree. Follow a globally optimal cut prefix. Maintain that every protected edge is absent from every optimal completion of that prefix (interpreted through the transport lemma). For the current, marking-dependent pair/case, choose the earliest branch containing an optimum. Its cuts are legal. Earlier A/BB branches lacking any optimum imply new protection is harmless by the pendant-exchange lemma; the protected-c form uses the symmetric exchange. BCY's omitted x branch is impossible by inherited exclusion. This induction accommodates case/selection changes because it applies local coverage at the actual marked state. The Lean branch lemmas prove the logical step, with the graph and coverage premises written explicitly.

## Meaning and use of the local tools

- `reference.py`: slow exact minimum over leaf partitions with equal rooted restrictions and vertex-disjoint minimal embeddings. Reach for it only on tiny inputs. Output is optimum cuts and a partition witness. It shares no algorithm code with the reconstruction, but authorship and input interpretation are shared.
- `algorithm.py`: all source branches in the labelled-rho convention. Output is a decision; `SemanticHole` is an unresolved input/state interpretation, never a false decision. It is a tested reconstruction, not a certified library implementation.
- `replay.py`: runs frozen controls first, then finite exact comparisons. Every receipt names the denominator, source hashes, timings, cases reached and failures. It stops at its first mismatch. The wrong-answer comparator control must fail before any real comparison runs.
- `ProtectedBranch.lean`: conditional optimal-family logic and concrete Boolean suppression invariants. Standard-library axioms only, explicitly printed. The caller must prove its forest state satisfies every hypothesis.

Fresh-author adversarial replay and graph-level formalization remain required. Finite matching is not the campaign acceptance gate.

## Root-safe normalization

An executed three-leaf state shows the undefined-parent case in Lemma 6.5. Take F1 = rho→((a,c),b), and F2 with components {rho} and ((a,b),c). Let E contain the three leaf-parent edges ea, eb, ec, and E2 = {eb}. Cutting E yields singleton components, hence an AF; cutting E2 makes a,c common siblings. The path-cut set E1 contains ea and ec, while their LCA is the unlabelled root of its F2 component. The expression eu in the lemma therefore has no edge to name. The direct-deletion replay also confirms that E\E1 = {eb} yields an AF. See `root_normalization_witness.py` and its result JSON. This is a defect in the general formula's domain, not a false output of Figure 6.5.

The needed replacement is: after pendant cuts make a,c siblings, remove the selected path cuts; restore the LCA parent edge only when at least two path edges were removed **and that parent edge exists**. The root case requires its own proof of AF preservation.

Given this replacement, the two-pendant exchange reduces to an explicit counting argument. Start with an optimum E containing endpoint z and at least one pendant edge. Add whichever pendant edge is missing (at most one), then apply normalization. At least one path edge is removed. Removing one restores no edge; removing at least two restores at most one. The pendant edges are off the path and remain cut. Thus the result has at most |E| cuts and contains both pendants. Minimality makes it an optimum. `normalization_cost_le` proves the cardinality inequality in Lean. The remaining mathematical premise is the root-safe normalization's AF preservation, together with transport through the active-state contractions.

## Current checks

The deterministic implementation matches the partition reference on all 225 ordered four-leaf pairs, all 11,025 ordered five-leaf pairs, and 3,000 six-leaf pairs sampled with seed 613. Every decision budget from -1 through the reference optimum plus one was checked. The six-leaf sample reaches BCY 90 times and protected-c A2BC 136 times; the result file contains example traces. A separate 80-state cutset enumeration checks 160 endpoint instances of the exchange statement. Seven local Lean theorems compile; the four branch logic theorems use no axioms, and the Boolean/counting theorems use only `propext` and, where printed, `Quot.sound`. The deliberately false negative-control theorem is rejected.

The source-level running-time proof, convention conversion, full graph proofs and fresh-author verification are outside these completed checks. No universal correctness or improved-bound claim follows from these results.
