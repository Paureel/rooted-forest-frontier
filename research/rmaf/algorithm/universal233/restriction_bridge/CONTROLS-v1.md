# Fixed exact controls, version 1

Pinned 2026-10-15 before universal proof development. Lean kernel `decide` must establish each listed Boolean equality; an opposite asserted equality in FalseControls must fail. These are construction controls, not a universal census or independent verification.

Let `T = ((0,1),(2,3))`, `Q = [[0,1],[2,3]]`, and `F = [[0],[1],[2,3]]`.

1. Nested restriction: restrict `[1]` after `[0,1]` equals the original restriction `[1]`, both `leaf 1`.
2. LCA below input root: restriction `[0,1]` is `(0,1)` while original minimal vertices are `[[false],[false,false],[false,true]]`; the original root is absent. Restriction `[1]` is `leaf 1`; its minimal embedding in `(0,1)` is `[[true]]`.
3. Disjoint local embeddings: the literal F subfamilies are `[[0],[1]]` and `[[2,3]]`, each an agreement family in the corresponding literal restrictions. F is an original agreement family.
4. False reverse without original Q-disjointness: `Qbad = [[0,2],[1,3]]` partitions the labels. Each local singleton family on its restrictions agrees, yet original `agreement T T Qbad = false` because its two embeddings share the root.
5. Refinement direction: every F block is contained in a Q block, whereas not every Q block is contained in an F block.
6. Exact cost: local costs are `1+0=1 = 3-2`; the alternate `3-1=2` is false.

Fail conditions: a clean equality fails to elaborate; any paired false equality elaborates; any nonstandard axiom enters production; any source/module origin differs from the retained source manifest. No failed control may be erased or weakened.
