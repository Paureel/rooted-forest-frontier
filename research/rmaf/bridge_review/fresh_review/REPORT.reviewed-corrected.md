# G1 graph-convexity theorem

Lean checks that every finite nonempty connected support in the binary-address graph has a minimum-depth root and satisfies `PureBridge.RootedRegion`. The proof retains the full vertex support. This proves the graph-support part of G1; construction of that support by the campaign's executable hull extractors remains unverified. G2–G7, the unrestricted faster bound, safe coverage, and the Whidden prior-bound reconciliation remain open. No novelty claim is made.

## Formal result

`lean/GraphRegion.lean` defines adjacency by appending or deleting exactly one Boolean (lines 9–10) and connectivity by finite graph walks (lines 12–14). The proof chooses a minimum-length vertex from the finite support, derives that every support vertex descends from it, and proves that every intermediate ancestor also belongs to the support. Neither ancestry nor convexity is assumed in `ConnectedSupport` (lines 87–91). The root constructor uses `Classical.choose` and is noncomputable.

`ConnectedSupport.toRootedRegion` (lines 106–112) has the same membership predicate as the original support. `root_unique` proves that any independently computed minimum-depth vertex agrees with the chosen root. The `MinimalEmbedding` wrapper records terminal inclusion and least connected support. Its address lists impose no unique-label, terminal-leaf, or ambient-tree invariant. The theorem uses only its connected support; it does not construct an embedding, prove a leaf-address encoding, or identify any existing executable extractor with this wrapper.

The replay script `audit_lean.py` recompiles the unchanged `PureBridge.lean` dependency into the review directory, compiles the two new proof files, records source hashes and axiom reports, and checks the false controls. It checks 18 new theorems, including six control theorems; definitions and the 16 imported theorems are excluded from that count. The only reported axioms are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. Three false controls are rejected with Lean's explicit falsity diagnostic: omitting connectedness, omitting the minimum-depth hypothesis, and treating a two-bit extension as one graph edge. The true one-bit edge passes using the same tactic as the last false control. The certificate is `lean/audit/certificate.json`.

## Interface trace

| Existing use | Hypothesis needed | Result of this review |
|---|---|---|
| `PureBridge.lean:23`, `deepest_root_in_neighbor` | `RootedRegion` for both input embeddings | Graph supports produce the exact structure; `GraphRegion.lean:123` composes the original theorem with that construction. Executable support extraction remains unproved. |
| `PureBridge.lean:35`, `deepest_neighbors_intersect` | Each neighbor and selected component realize a rooted region, with the printed depth and overlap hypotheses | `GraphRegion.lean:131` proves the graph version for any number of neighbors by pairwise use of the same selected root. |
| `PureBridge.lean:75`, `freeLeft` | Avoiding the common root clears every other embedding | Open universally. Independent finite tests exercise avoiding subblocks on both sides of pure overlaps. |
| `PureBridge.lean:76`, `freeRight` | Avoidance by the entire remainder permits every valid local choice | Open universally. The finite completion comparison checks all deepest ties and all local minimum witnesses. |
| `PureBridge.lean:79`, `clearRest` | Repair the whole globally feasible remainder for at most one extra cut while preserving all old marks | Open universally. The source-side tests split one matching piece and check both embeddings; the whole-state tests retain initial marks and remaining disjointness. |
| `role_swap_minimum` and `role_swap_parameter` | Equal marked/region partition families; at least r pieces; h≤d+r−1 | Open universally. The finite comparison reconstructs fresh suppressed region trees, compares every feasible partition, and checks the optimal ordinary forest's refinement. |
| Recursive algorithm, termination and recurrence | Exact attained local queries and all elimination invariants, plus a safe cover for arbitrary instances | Open. No recurrence or faster base follows from the new graph theorem. |

The original `free_replacement` uses `freeLeft` at line 98, and `free_minimum` uses it directly at line 152. The paid replacement uses `clearRest` at line 115 and `freeRight` at lines 116 and 120. Those are structure fields. Compilation of either identity cannot prove those fields for actual agreement forests.

## Exact finite evidence

The independent verifier was written after freezing hand controls and before reading candidate implementation code. Its graph paths use breadth-first predecessor searches; its forest enumeration uses leaf set partitions. It imports no earlier campaign oracle and no original pure-bridge implementation. The same review code supplies the core graph functions to the local and completion comparisons, so those comparisons are not separate independent implementations of each other.

| Check | Executed scope | Exact result |
|---|---|---|
| Frozen controls | 18 hand-derived fields, with two documented pre-execution transcription corrections | All passed; 20 deliberately wrong answers or path/region counts rejected. |
| Geometry | All 125 rooted unordered labeled target trees with 1–5 leaves; all 5,703 leaf partitions | 5,283 pure partitions, 816 deepest-neighbor checks, 5,664 avoiding-subblock checks, 6,820 degree-two target splits, and 258,247 mark/region containment checks; no counterexample. |
| Local source transport | All 23,614 target/source/subset cases in the stated 2–5-leaf pool | 165,256 degree-two source/target split transports; no counterexample. |
| Marked role swap | Every unlabeled-vertex mark subset for those local cases | 373,634 equalities between marked and region feasible partition families, 11,384,296 partition comparisons, and 373,634 checks of h≤d+r−1 and q=h−(r−1)≤d; no counterexample. |
| Empty/root regions | Included in the same role-swap comparison | 138,786 queries with a leafless region relative to the local label set; 186,817 root-mark queries. |
| Complete elimination | All 2,340 overlapping pure forest cases on 4–5 target leaves, plus one 6-leaf clique; empty initial marks and one seeded arbitrary initial-mark profile per case | 4,682 profiles, 14,940 feasible exhaustive forests, 6,204 elimination outputs over all deepest ties and all local minimum witnesses; each output is feasible and attains the exact optimum. |
| Supplied multi-mark example | Target `((0,3),(1,(2,4)))`, source `((0,2),1)` | Ordinary, first-mark, second-mark, joint-mark optima are exactly 1,1,1,2. This is a reproduction after reading the candidate example, not a blind planted control. |

These finite checks test semantics and excluded hypotheses. They do not prove the general split-transport or exchange lemmas. The role-swap scan took 70.35 seconds after a same-code projection of about 64 seconds with a 90-second allowance; no larger run was launched. Receipts retain exact counts and source hashes under `../results/bridge-review-*.json`.

The fresh reviewer found that the original two-bit-edge control failed because a decision procedure was unavailable; a true edge failed identically. That rejection did not detect falsity. The corrected control unfolds adjacency before calling `decide`, its true twin passes, and the audit requires the exact falsity diagnostic. The superseded certificate and failure log are retained in `lean/audit/pre-control-fix/`.

## Provenance and remaining work

The shared mathematical inputs are the user-supplied pure-bridge candidate, ordinary rooted agreement-forest definitions, and later the candidate formal statements. The independent Python code and its hand controls do not depend on original oracle outputs. The Lean proof deliberately imports `PureBridge` to check the actual consumer; this is a formal composition, not an independent reimplementation of that theorem. All finite tests performed here are discovery evidence for subsequent work; they cannot later be relabeled as held-out certification of a theorem designed using them.

A full G1 executable certificate still needs a theorem that converts each well-formed labeled tree and nonempty leaf subset into the connected support represented here, retaining every unsuppressed vertex and preserving label addresses. The next exchange proof needs G2's whole-overlap assertion and G3's transport of a target split through rooted restriction equality, including the root case. G4 then requires applying that split to the unique globally occupying piece while preserving the other pieces and all marks. G5 and G6 require universal marked-region equivalence and the r−1 refinement bound. This review supplies no new evidence about the unrestricted safe-cover conjecture or the prior 2^q algorithm.
