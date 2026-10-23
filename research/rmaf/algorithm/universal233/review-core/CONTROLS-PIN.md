# Review controls pin, 2026-10-15

Frozen before fresh replay/control search. These controls test the reviewer, not universal truth by finite examples.

## Lean path

- Clean: compile all five frozen modules from copied source, with no preexisting oleans.
- Audit: enumerate every environment declaration under `Universal233` (including generated declarations), collect transitive axioms; allow only `propext`, `Quot.sound`, `Classical.choice`. Deliberately add an unproved custom axiom to a separate plant file and require the same audit to reject it. Remove one expected audit record in a copied log and require parser rejection.
- False: copied FalseExactPartition, FalseOneBranch, FalseRootCut must fail because their `decide` propositions are false. A standalone `example : True := by decide` twin must compile.

## Fresh exact graph evaluator

Share only binary rooted tree mathematical specification, no author graph/prototype imports. Vertices are tuple child addresses, adjacency from an independent explicit parent edge list. Partitions enumerate leaf owner restricted-growth strings; nonminimal connected supports enumerate internal vertices as free or assigned to a block and are checked by BFS. Every graph predicate must accept a hand-constructed valid support and reject overlap, disconnectedness and foreign-terminal plants.

Known fixture: tree `((0,1),2)`; owners 0→0,1→1,2→2, color 0=1=0,2=1. Third-block support contains root, cherry parent and leaf 2. Correct surgery gives merged support `{cherry parent,leaf0,leaf1}`, third support `{root,leaf2}`. Keeping parent in third support must be rejected for overlap. Root-cherry singleton fixture and singleton tree are null/boundary cases.

Finite census: all ordered full binary tree shapes at n=2..5, labels 0..n−1 in traversal order, all leaf partitions and all internal vertex assignments free/used-block, retaining connected terminal-exact disjoint supports. Colors enumerate partitions of used blocks (so all monochromatic colorings modulo relabeling). Demand mixed alternative, unique-color singleton and coarsening validity/refinement for every applicable case. Separate n<=4 pilot before n=5; stop/restructure if projected cost is excessive. Extra leafless-support cases are explicit fixtures, since SourcePartition permits them.

Misleading claims plants: (1) exact partition preservation rather than coarsening must fail on three singleton blocks above; (2) unchanged third-block parent occupancy must fail; (3) distinct nonroot addresses + #blocks=#cuts+1 implies realized cuts must fail on a syntactically shaped fake Output with a nonexistent address. Universal coverage/mass/runtime remain OPEN regardless of finite counts.
