# Normalization consumers after the adversary phase

Status: open proof obligations, not a correctness theorem. Source locators below use the thesis's printed pages; add13 for PDF pages. The general arbitrary-cutset normalization statement is refuted even when F1 and F2 are connected and their component-containment condition holds. The surviving variants must explicitly control compound endpoint root fragments.

A root fragment of an endpoint v means the connected component of v in the original-edge deletion F2−E, restricted to descendants of v. A surviving fragment contains a labelled descendant. An intact atom is a stronger condition: E contains no edge internal to the common subtree represented by v. The two conditions must not be conflated. A surviving fragment may be a proper subtree of the represented atom.

## Consumer map

| Source use | Cutset supplied by the source | Obligation before normalization | Obligation after normalization |
|---|---|---|---|
| Lemma6.5, pp101–103 | Arbitrary AF cutset E, subset E2 makes a,c siblings | Original statement lacks a surviving-label premise for compound a,c. The one-path-cut proof's label connected to the LCA (p102) need not exist. | Root-safe formula must handle missing LCA-parent edge, preserve the actual AF, and count original edges. |
| Lemma6.10 first exchange, pp112–113 | A minimum completion E0 extending a local prefix E; add both pendant edges | Establish surviving root fragments for a,c from minimum E0 or intact active atoms; added pendant cuts must stay outside these subtrees. The source removes E3 from the prefix, so identify its relation to all path cuts of E0 explicitly. | F2−E0' must remain an AF of the original trees, with both pendant cuts retained and the claimed size bound. |
| Lemma6.10 second exchange, p113 | E0' after the first exchange and pendant cuts; it need not already be minimum | Pair(x,u) is compound in general. Prove that x and the reconstructed u still have surviving root fragments. It is insufficient to prove a theorem only for ordinary labelled leaves or to invoke minimality of E0' without justification. | Handle missing parent of the new LCA; retain both pendant cuts; account for cuts restored/removed in the same original-edge universe. |
| Theorem6.12 ordinary A2BC exchange, p116 | Minimum E0 containing ec and one pendant edge | Add the missing pendant edge, preserving endpoint fragments, then normalize the a–c path. The source's formula restores ec alone; relate this partial restoration to the full path normalization statement. | Obtain a minimum completion containing both pendant edges. This is existential exchange, not membership in every optimum. |
| Theorem6.12 protected-c A2BC | Not explicitly written in pp115–116 | Supply endpoint-swapped exchange with the same active compatibility, anchors and provenance. | The selected A optimum avoids the two newly protected pendant edges. |
| Theorem6.12 protection persistence | Later residual completions on a promising path | Exact residual-to-original lift must preserve cost, chosen branch edges and any designated protected origin in a suppressed path. Root sibling equivalence needs its own graph statement. | Old protected edges remain excluded from every optimal residual completion. OR-ing flags only records a potential origin. |

## Existential interface boundary

Source Lemmas6.6–6.11 give equalities for optimum decreases after a branch. To supply the repaired logical interface, each equality must yield an original-edge optimum containing that branch's edges. A cutset lift/projection theorem is needed even when the scalar equality is accepted. Finite replay cannot replace this theorem.

The new logical consumers in ExistentialConsumers.lean take the graph exchange and lifting facts as explicit hypotheses. The unchanged reviewer file proves the endpoint-specific A2BC selection. The new file adds BCY selection and inherited-exclusion consumers. Their kernel acceptance proves this conditional logic only.

## Smallest live normalization question

For exact finite active forests with common compound endpoint subtrees, actual AF compatibility and containment: do nonempty endpoint root fragments suffice for root-safe normalization, with all edge operations interpreted before suppression? Separately, does minimum completion of the original common pendant subtrees ensure these fragments, and do the two Lemma6.10 transformations retain them? These are distinct obligations; the adversarial cutset has three cuts against optimum one and settles neither.

Global marked-state induction, decision correctness, runtime and convention transfer remain open regardless of this local repair's outcome.

## First review checkpoint

The initial questions above are retained as the construction record. The first fresh review now supports the restricted N_anchor normalization and minimum-common-subtree survival arguments as prose proofs. It also reconstructs a specific second-exchange transport argument: the only suppressed edges lie on the restored corridor, so all residual cuts and the second path retain their original current-edge identity. That new reviewer supplement is undergoing a second independent read. The source's general scalar-optimum-to-original-cutset lift and protected-origin lift are still open; no global marked-state theorem follows from this checkpoint.

See [first fresh review](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/review/REPORT.md) and [exact remaining imports](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/review/verdict.json). The AF arguments are prose; the separate Lean files check only their stated local graph, list, binary-cut, logical and arithmetic constituents.

## Second review checkpoint

The [second independent review](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/review2/REPORT.md) independently reconstructed and accepted the restricted normalization, strict empty-root repair, corridor transport and local consumer chain as prose. It rebuilt the original and version 2 Lean modules unchanged and rejected all three false controls. The graph-to-recursive-encoding/splice-witness bridge remains unformalized.

The smallest general open import is now precise: an optimal residual completion must lift to a minimum original-current-edge AF cutset containing the selected branch cuts with additive cost, choosing a designated protected origin on a compressed cut path when required. Later root-sibling replacement must preserve this relation. Until this is proved, sequential branch equalities do not supply the starting E0 of Lemma 6.10, raw existential coverage is still an input, and inherited protected-edge exclusion is still conditional. The reviewed two-exchange chain assumes that starting E0 explicitly; it constructs one residual AF and does not prove general equality of residual optima. See the consolidated [result](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/RESULT.md).
