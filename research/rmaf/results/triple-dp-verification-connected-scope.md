# Fresh connected-region replay

The independent replay passed in 1.4373423340002773 seconds. `ConnectedRegions.lean` contributed eight checked theorem audits; the freshly rebuilt `TripleDP.lean` dependency contributed 19. A separate positive-control theorem also compiled without axioms. These counts are separate from the earlier route-wide 28-theorem receipt, which this replay did not modify.

Source hashes:

- ConnectedRegions.lean: `1b09d6e197d26eef62dfa5b13b8f5e17e826867e8778e68b50bc4f7b02d8ea33`.
- NegativeConnected.lean: `9ea7ecb0d1121d68039e31db6634e63da5f7e43e2e11d250f552b74d9a391d12`.
- TripleDP.lean: `6b544504b68dd6638caa40200914dee5720be1cdc38ce5f180de1dc792944298`.

The fresh script `research/rmaf/triple_dp/verification/replay_connected.py` read no author audit implementation. It copied the pinned sources into its own `verification/connected_replay` directory, rebuilt the dependency and extension into its own `deps` directory, and supplied only that directory in LEAN_PATH. Hashes were checked before and after execution. Exact commands, return codes, axiom names, durations, and log hashes are retained in `research/rmaf/results/triple-dp-verification-connected.json`.

## Statement scope

`ConnectedRegions.lean:7–14` defines OnPath by list prefixes around the LCA, PathConvex by closure under all such path vertices, and PrefixClosed by closure under prefixes. The objects are predicates on binary addresses. These definitions do not introduce a finite tree, labelled leaves, colors, region families, or costs.

At lines 16–31, the file proves that the LCA is a prefix of its left argument and that path convexity implies the earlier LCA-closure property. Lines 33–41 prove that a region containing the root is path convex exactly when it is prefix closed. Lines 43–55 prove child-restriction path convexity and inclusion of an occupied child's root.

The main theorem at lines 60–83 assumes `region []` and proves both directions: the whole region is path convex exactly when each child restriction is path convex and every nonempty child restriction contains its child root. This establishes the stated single-region decomposition for path-convex address regions. The proof does not merely assume the desired equivalence: its reverse implication reconstructs prefix closure using the two child hypotheses and then applies the proved root-prefix equivalence.

Lines 87–98 formalize the previously supplied gapped region {root, left-left grandchild}. It is LCA closed and fails path convexity because it omits the intervening left child. That example originated in the verifier's earlier report and then entered the author proof; it is shared input, not new independent numerical evidence. The new Lean derivations themselves passed kernel checking.

## Controls and remaining obligations

`NegativeConnected.lean:5–7` asserts the false membership `gappedRegion [false]`. The replay rejected it specifically because `decide` proved `[false] = [] ∨ [false] = [false, false]` false. The log contains no missing-module or object-file failure. A fresh clean twin, `gappedRegion [false,false]`, compiled through the same imported extension. The eight extension axiom reports use only subsets of propext and Quot.sound; the dependency reports use only the previously allowed standard axioms. The accepted source scan found no sorry, admit, unsafe, or custom axiom declaration.

The comment at lines 3–4 correctly excludes the cost-preserving family theorem G2. The new results do not establish a labelled, nonempty-region normal form; preservation of pairwise family disjointness and coverage; the correspondence with colored/masked DP states; cost preservation; source-component suppression G1; or the Python implementation link G3. The equivalence between this address formulation and any separately defined finite graph model must also be stated when that model is used. Empty or leafless regions are not excluded by PathConvex alone.

Verdict: the eight stated supporting theorems reproduce, and both the negative control and clean twin behave as expected. Single-region path-convex address decomposition is kernel checked. The full G2 family/cost correspondence and terminal MAF theorem remain OPEN.
