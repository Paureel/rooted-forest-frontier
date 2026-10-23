# Candidate pair-case reduction

The proposed replacement for `PairSplitGoodOutside` separates a target-geometry test from a source-profile test. The profile theorem is checked in Lean. The target selector argument and the agreement-forest exchange below are proposed universal proofs that still need formalization and nonauthor review. The actual source generator's coverage, trace grammar, original-edge realization, and state history remain required inputs. No complete faster algorithm or new runtime is established here.

## State and tests

Use original-label sets in a fixed original rooted binary target tree T. The current source forest has overlapping parents A,B and an isolated homeomorphic parent C, with earlier rules and tidying applied at their actual guards. Let H_A,H_B be the minimal target embeddings of A,B. At each shared vertex v, count the realized leaf regions of each parent after deleting v; an occupied nonlabel vertex has two or three such regions.

For a binary boundary, let A1,A2 and B1,B2 be its two color classes in each parent. Call the boundary mutually clear when both explicit tests hold:

- each H_Ai is disjoint from H_B;
- each H_Bj is disjoint from H_A.

The tests involve actual full target embeddings. Merely avoiding the selected boundary vertex does not imply them. These tests also imply the four sector embeddings are mutually disjoint. Arbitrary disagreement inside a sector is allowed.

## Target selector

A shared vertex with three realized regions in either parent gives a binary ownership cover with one r=3 source core and one r>=2 core. The conditional raw residual bound is at most 1/c+1/c^2, which passes the full recurrence at c=233/100. This case uses no good-parent exchange.

Suppose every shared vertex has exactly two realized regions for both parents. Then each parent embedding has degree two at every vertex of their intersection H. Convexity makes H connected, and its maximum degree is two. The intersection cannot consist of a single vertex: two sets of two incident directions in an ambient degree-at-most-three tree share a direction, so the adjacent vertex would also be shared. Hence H is a nontrivial finite path.

At an internal H vertex, neither parent has an exterior branch. At an H endpoint, each parent uses its one common path direction and one exterior direction; the two exterior directions differ, or H would extend. All A and B leaves therefore lie in the four exterior sectors. A minimal embedding of labels confined to one sector cannot include the path endpoint, because it reaches that endpoint in at most one direction and the endpoint is not a selected label. Thus any edge of H induces a mutually clear binary boundary. An original root has ambient degree two and can only be internal in H, so no artificial stem is needed.

This argument must be rebuilt against executable `minimalVertices`, including the degree/realized-region correspondence. Until then, an implementation should compute and check the mutual-clear predicate and report an unsupported state if the proposed implication fails. The finite records contain examples of both selector alternatives, not a universal geometry census.

## Profile reduction

The proposed actual two-color source trace consists of full binary mixed-cherry decisions followed by one forced final unit cut on every path. Under that grammar, the raw one-, two-, and three-emission profiles are [1], [2,2], and [2,3,3]. The Lean theorem `at_least_four_extremum` bounds every full trace with at least four emissions by [2,3,4,4] at c=233/100. `four_plus_any_safe` then gives the sufficient full vector [1,1,3,4,5,6,6], whose exact mass is 159752208278600/160005726539569<1.

If neither core has raw profile [1], their combined raw mass already passes. The remaining pairs have one [1] paired with [1], [2,2], or [2,3,3]. In each pair, increasing any single emitted cut charge by one makes the full recurrence pass. The least favorable increases give [1,1,3,4], [1,1,3,4,5], and [1,1,3,4,5,6]. Increasing a shallower emission reduces mass more.

Raw profile classification does not require unbounded generation of every output. Traverse the unpruned source trace until it finishes or produces four raw emissions. Before four emissions, at most four source-depth paths are explored; each actual operation reduces the number of live groups. This gives polynomial classification work once the source trace and operation-size invariants are supplied. Actual budget-pruned generation still has its O*(2^q) prefix cost, which must be included in the full running-time proof.

## Mutually clear binary case

Assume A has profile [1]. Its actual single source cut must produce exactly the two whole color classes A1,A2. Assume first that both original parents A,B are non-homeomorphic.

If either Ai is non-homeomorphic, execute the A-clear output. Its components A1,A2,B,C have disjoint target embeddings, by mutual clearance and the boundary split. At least two of those actual parents are bad: the chosen Ai and unchanged B. Exact depth-one pretests assign lower bounds 0,1,2, with 2 only after every one-cut trial fails. If one query remains unresolved, another bad parent removes at least one budget unit. If p>=2 remain unresolved, each query loses at least 2(p-1), and the entire p-query mass is at most 1/c. If no query remains, the state is polynomial. Thus this one A-clear emission has genuine unit progress. No cut already used to clear A is charged again.

If both A1,A2 are homeomorphic, the actual A-core cut is a valid local solution using one cut. Since original A is bad, its exact local optimum is one. In every B-clear output, mutual clearance isolates unchanged A from all B pieces and C. Complete A with that specific one-cut solution and subtract one from the remaining budget before any residual B work. The completed cut belongs to A; the generating core cuts belong to B. Their original source namespaces are distinct. This remains valid if the B pieces overlap one another or contain arbitrary hard subtrees. Every B-clear emission consequently has genuine unit progress, while the A-clear output receives its ordinary bound.

This proof uses a specific local source cut rather than an assumed bonus for an unresolved query. In particular, an unrelated sole unresolved query may retain its entire remaining budget; the n10/n15 first selector records contain exactly that zero-loss situation.

## Homeomorphic parent exchange

If A is homeomorphic, a mutually clear binary boundary should permit retaining A intact and emitting only the full B-clear source core. Consider any final agreement forest refining the current source parents. At most one B block crosses the binary boundary, because two crossing blocks would overlap on the target path. If no B block crosses, replacing all A blocks by A is safe: the B blocks lie in sectors disjoint from H_A, and C was isolated.

If a B block crosses, A has at least two blocks. Split that one B agreement block into its two boundary portions. Its agreement with its target restriction supplies one actual source cut for this split. Merge all A blocks into the homeomorphic parent A, saving at least one component. The new forest has no more components, clears B, and keeps A intact. Source parents are distinct, so modifying A does not reuse the new B cut. Mutual clearance supplies target disjointness after the replacement.

The exchange concerns a final agreement block, whose rooted source and target restrictions agree. It does not claim that the entire original B can be cut into B1,B2 with one source cut. B may require several cuts to clear, and the algorithm emits its full paid source core. The resulting conditional residual mass is at most 1/c. The symmetric exchange applies when B is homeomorphic. Both-homeomorphic cases remain with the earlier attributed isolated-group completion.

The exchange is restricted to two boundary colors. A three-region split can cost two cuts while merging A saves only one; the false three-region extension is retained in the workfile and rejected by a control. The source graph surgery, original-edge lift and agreement validity of the exchange remain open formal obligations.

## Executed evidence

The source-bound author replay compiled five modules, including unchanged RMAF/CoreGraph/CoreProgram copies, and audited all 25 new theorems. Four deliberately false controls were rejected because Lean proved their propositions false. Only standard Lean axioms occur. `algorithm-scaffold-profiles-formal-receipt-v1.json` records source hashes, exact declarations, logs and timings. The genuinely source-code-specific statements prove normalization of arbitrary pure subtrees and a one-cut run for two pure root children; they do not prove the full source trace grammar.

The controlled n10/n15/n19 continuation calculation reconstructs every emitted core cut in the original source alongside the actual two pendant cuts. It tests earlier-rule exclusions, selected-cherry admission, tidying, all inequivalent shared-vertex color selectors, exact local one-cut trials, and isolated all-good completion with explicit source cut witnesses. Additional cuts for an all-good overlap group equal its target Fitch score minus (number of source parents minus one). Charging the whole Fitch score would overcount.

For n15, the expensive [1]+[2,3,3] selector has one progressing emission and full continued mass 158752208278600/160005726539569<1. A three-region selector is already safe before continuation. For n19, its binary mutually clear selector reproduces [1,1,3,4,6,6] and mass 157422208278600/160005726539569<1. The proposed good-parent exchange would instead keep only the bad parent's [2,2] core, with conditional full mass 2729867400/2947295521<1. These completed contacts were read during development and cannot certify this argument independently.

## Required completion

The first source obligation remains the actual two-color trace/coverage/original-cut theorem, including root, suppression, forced steps, budget pruning and original-label history. The first new target obligation is the selector theorem connecting realized regions and executable minimal embeddings to a mutually clear boundary. The exchange surgery needs its own formal graph proof. The attributed polynomial completion and exact disjoint-query decomposition still require their consuming source/history hypotheses, and the complete solver needs every other scaffold case, termination, generation cost and a nonauthor reconstruction. All three main algorithm milestones remain open.
