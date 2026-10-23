# Frozen independent instrument design v1

Frozen before implementation or new construction tests, 2026-10-15.

Scope is literal SPEC-CB1. No production implementation is imported or read.
The only mathematical imports are the explicit conflict definition (PROOF.md,
Definitions), the stated incidence-column quotient (C4), and the ordinary tree
model. Toolkit index and conflict README were consulted. Existing exact tools
are development-lineage instruments; a new one-shot codebase is justified by
the requested no-code-reuse fresh check. It remains beside this problem.

Tree parsing: keep the literal nested tree, attach integer vertices in preorder
and original edges in preorder parent-child traversal. Rooted restriction for
the partition oracle is recursive leaf deletion followed by unary suppression.
For H triples use a separate deepest-pair-MRCA comparison from parent chains.
For H pair paths use original undirected vertex and edge paths. Enumerate all
set partitions for small ordinary controls; require equal rooted restrictions
and disjoint original vertex supports in both trees. This yields independent
ordinary optimum costs as component count minus one, without using conflicts.

Implement the abstract candidate directly from the frozen description:
minimal rows; connected incidence factors; at each search node rederive every
nonempty column, remove dominated columns, canonically retain the lowest
original edge in each maximal equal-column class; replace/minimize rows;
choose (cardinality,integer-mask) minimum; branch increasing edge id; return
first witness. Iterative deepening per original factor, without memoization,
includes all rejected budgets. Count every recursion node and maximum chosen
row rank. Also brute-force abstract transversals for frozen controls.

Certificate verification re-derives source cut connected components and leaf
partition; checks charged cost equals cut cardinality and component count-1;
checks literal labels and equal restrictions; and compares submitted target
support vertices against freshly computed original supports. Ordinary controls
must recover all 9 expected literal optima; all 6 abstract controls must recover
optimum and factor counts. Every nonempty ordinary fixture has a clean
certificate twin and three rejected corruptions (+1 accounting, missing label,
wrong support). Empty baseline exactly zero. Exact false bound 3/2>=2 is rejected.
A corrupted expected optimum for the crossed quartet must fail comparison.
All these controls run before any new family test; failures suspend that leg.

Adversarial candidates, after controls: measured small matched-sector and
order-reversed caterpillar pilots, then targeted constructions motivated by
those exact outcomes. No broad tree census, no blind packing or centroid
heuristic. Aim is an infinite realized lower family or an exact semantic
counterexample; if neither emerges report an exact connected-factor rank
barrier and the missing runtime lemma. Finite node counts are only measurements.
Reduced eligibility is separate: ordinary legality, common pendant subtrees,
and common chains must be described; no reduced claim follows from legality.
