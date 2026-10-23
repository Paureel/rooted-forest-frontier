# Assembly interface and provenance

| Consuming claim | Exact author theorem |
|---|---|
| Every emitted source output has original partition and disjoint embeddings | `SourceValidity.lean`: `generated_source_valid` |
| Actual partition check forces three distinct parent label sets | `ForestOutputs.lean`: `parent_partition_disjoint` |
| Clique ownership returns one of three actual source-valid generated members | `ForestOutputs.lean`: `clique_forest_cover` |
| Chain ownership returns one of four actual source-valid generated members | `ForestOutputs.lean`: `chain_forest_four_cover` |
| Middle joint cardinality two returns the paid diagonal alternatives | `ForestOutputs.lean`: `chain_forest_diagonal_cover` |
| Exact request color versus original target clearing | `Requests.lean`: `request_mono_iff_clear` |
| Original refinement and original nonredundant source-cut realization | `Requests.lean`: `requests_whole_source` |

All theorem names are in `Universal233.Assembly`. `ForestBranchSolution` is a conclusion-only abbreviation for a literal generator member and its proved properties. It is never a field that assumes existence, safety, coverage, or runtime. `RefinesBlocks F Q` means every original block of F lies inside a block of Q; local cut-subset containment is not required.

The only two source-copy adapters are the cut module filename `Coverage` -> `CutCoverage` and the corresponding first import of its `InitialCoverage`; the successful receipt lists each original and copy hash. Development contact includes the completed geometry/core/coverage/cut proofs and their audit instruments. The finite pilot is development evidence only. Independent whole-source mass construction was not read before this package's freeze. The separate hard-parent arm was read only after its completed freeze. No novelty claim or complete algorithm claim is made.
