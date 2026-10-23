# Binary parent exchange E

`BinaryExchange.binary_exchange` proves the partition exchange requested in TARGET-v1 E against the original executable `RMAF.agreement` definitions. The author replay passed with only Lean's standard axioms. The grade is **AUTHOR-LEAN**: fresh nonauthor semantic review and the full consuming-interface trace remain pending. This result does not complete the rooted-MAF algorithm or its running-time bound.

The source is `Exchange.lean:88`; the immutable replay is `research/rmaf/results/algorithm-pair-case-exchange-20261015T083439Z/`. The manifest records source hashes, compiler results, and the complete originating-module inventory. Rebuild from the workspace root with:

```sh
./bootloops-python research/rmaf/algorithm/pair_case/exchange/sol-binary-e-20261015/replay.py
```

## Statement

Let S,T be original `RMAF.Tree` values with distinct leaves and equal leaf sets. Let P pass `partitionCheck (leaves S)` and `pairwiseEmbeddings S`; choose distinct members A,B. Let `treeAt T v = some u` with nonempty original address v, and put D=`leaves u`. The address v is the child endpoint of a literal original downward target edge.

The four sectors A∩D, A\D, B∩D, B\D must be nonempty. Each A sector must have actual target embedding disjoint from whole B, and each B sector must have actual target embedding disjoint from whole A. Every other P block must have target embedding disjoint from both A and B. Finally, `restrictionAgrees S T A = true`. These are explicit hypotheses of the theorem; it assumes no whole-B restriction agreement.

For every original F satisfying `agreement S T F = true` and `Refines F P`, the executable `exchange A B F u` returns F' with:

- `agreement S T F' = true` and `Refines F' P`;
- exactly one block equal to A;
- every F' block contained in B contained wholly in D or wholly outside D;
- `F'.length ≤ F.length`;
- exact equality of the filtered outside-block lists, `outside A B F' = outside A B F`.

`Sub C A` means every label of C belongs to A. `Refines F P` means every F block is contained in a P block. `inside` is its executable Boolean counterpart. `Disj T C E` is defined using actual original-address hulls; `VertexGeometry.executable_disjointVertices` in the imported Bridge.lean proves its equivalence to the original Boolean collision test. No exchange, selector, or cut-cost conclusion occurs as an assumed structure field.

## Construction

The function divides F into U (blocks inside A), V (remaining blocks inside B), and W (remaining outside blocks). `BinaryExchange.grouped_perm` proves that U++V++W is a permutation of F, and `BinaryExchange.apart_partition` proves that U partitions A. The output is A followed by the nonempty D and non-D sectors of every V block, followed by W. All label counts are preserved.

For each final C in V, `BinaryExchange.descendant_agreed_split` proves that D∩C is a rooted cluster in the restricted target, transfers that cluster through C's rooted S/T agreement, and lifts it to the original source. The theorem proves that the two sectors have disjoint actual source and target minimal embeddings. The proof retains original unary paths: `BinaryExchange.cluster_disjoint_span` separates the true-sector minimal hull from the false-sector rooted span.

Every mixed final C occupies original target vertex v (`BinaryExchange.crossing_occupies`). Since F has disjoint target embeddings, at most one V block is mixed (`BinaryExchange.mixed_blocks_at_most_one`). If one is mixed, the nonempty A sectors lie in two different U blocks; otherwise that U block and C would both occupy v. Thus replacing U by A compensates for the possible additional B block (`BinaryExchange.exchange_size`).

`BinaryExchange.exchange_valid` proves all five constituents of the actual agreement checker: both partition checks, every rooted restriction agreement, and source/target pairwise embedding disjointness. The original source parent disjointness permits merging A; target sector clearance permits merging A after V is split. `BinaryExchange.binary_exchange` derives the displayed decomposition from arbitrary F and combines these statements.

## Literal source witness

`BinaryExchange.descendant_final_source_edge` in SourceEdge.lean at line 54 proves a further statement. For a mixed **agreed final C**, it constructs a nonempty original source subtree address w and subtree z with `treeAt S w = some z`, such that, for every x∈C, x∈`leaves z` iff x∈D. The subtree can contain extra labels outside C. This is a literal original source edge realizing the two colors on C.

The theorem applies to C after C's agreement is established. It gives no one-edge separation of the whole unagreed original parent B. The complete algorithm still needs the residual-source-state and cut-cost reconstruction argument that connects its actual emitted core operations to a surviving exchanged final forest. No declaration in this package states that argument.

## Executed checks

The final fresh directory contains no candidate development oleans. The replay rebuilt 14 scientific modules, audited **766 originating declarations**, and retained **24 compiler/audit/control runs**. Every originating declaration, including generated and private declarations, used only `propext`, `Classical.choice`, or `Quot.sound`; none was unsafe. `Audit.log` contains the per-declaration records. The source scan rejects `sorry`, `admit`, `native_decide`, and custom `axiom` declarations in the scientific modules.

Five deliberately false propositions were rejected with Lean's explicit `decide` false-proposition diagnostic: whole-B rooted agreement on T1; source separation of whole-B target sectors; an arbitrary noncluster color split of an agreed tree; a false root-boundary mixed-color claim; and a false absent-label embedding. A clean twin compiled and passed the same originating-module audit. The custom-axiom plant also compiled, then the audit rejected both its unused custom axiom and the private theorem depending on it. The detector checks those exact originating records and the exact forbidden-declaration count of two.

The pinned literal seven-label T1 input, all mutual-clear tests, and the six-block exchange compile by kernel `decide`. `T1.T1_universal_consumer` at line 32 explicitly applies the universal theorem to that input. A fresh canonical partition constructor, independent of X0 code, emitted 877 partitions, with 30 refining P and 15 retaining A whole. Both finite restricted minima were five (`T1.lean:26`, `:29`). Those are minima over the retained finite lists; this package supplies no separate formal completeness proof for that enumerator. The six-label root-promoted fixture verifies actual root overlap and the explicit surgery. The positive controls also retain a suppressed original path and reject absent labels by producing an empty embedding.

The unchanged original RMAF source took 5.510551 seconds in the final replay; the new T1 module took 0.887905 seconds. Every compiler invocation had a 60-second limit. No broad census, full toolkit suite, remote compute, or hosting was used. Earlier replay directories and failed development logs remain on disk.

## Review boundary

The preconstruction X0 no-fire was reported by the coordinator before this arm began. This arm read no X0 implementation, unfinished G work, profile proof argument, or core/referee implementation. The universal proofs depend on the original RMAF source, the permitted original-address Geometry/Bridge source, and the new source files listed in the replay manifest. ProductTopology.lean was read for a possible reusable join lemma but was not imported.

The first remaining acceptance step is a fresh nonauthor semantic review of the printed theorem hypotheses and conclusions, followed by the full consumer trace. The first remaining algorithmic step is the residual-source cut/reconstruction interface described above. Algorithm, Correctness, and Smaller-base remain OPEN for the complete project. No novelty or smaller-base claim is made here.
