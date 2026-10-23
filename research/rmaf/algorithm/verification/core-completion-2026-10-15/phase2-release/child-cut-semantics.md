# Bounded cut semantics review

Review role: nonauthor source-semantic inspection of the released cut package.
This review found no gap in the four requested semantic claims within the exact
scope below. It is a reading of author proofs, not a replication or a fresh Lean
build, and does not establish full algorithm acceptance.

## Record and method

The cut manifest SHA-256 is
`61658da7b8868079dc471b82965da66e095beafbde509a726c5b930bed84a182`.
The source-coverage manifest was hash-checked only; its SHA-256 is
`a153e4e878c2cde3bea73f604a01a4955ca1b8fd94e8baa1bc02833934f32e33`.
All source hashes listed below were obtained with `shasum -a 256` in this review
and agree with the cut manifest's `exact_source_import_pins` for the inspected
files. The ten requested cut sources were read completely. Named dependencies
were inspected for the definitions and proof premises used in the traces below;
that inspection was selective for the geometry files, RMAF, CoreInvariants,
Branches, CutRecords, and Composition. It was not a second full dependency audit.

I used the reading-contract and independence-bookkeeping skills to distinguish
source facts from review inferences. I did not read live `core_work`,
`whole_source_mass`, assembly sources, pair-case geometry/exchange sources, or the
main workfile. No author was contacted or steered, no child agent was spawned,
and no frozen file was changed. No Lean build, numerical experiment, or toolkit
validation suite was run for this bounded reading task.

## Read: original components

`RMAF.Tree` is a nonempty binary tree with labels only at leaves
([RMAF.lean:8](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/lean/RMAF.lean:8)).
`CoreGraph.Valid` uses actual subtree lookup, and `CoreGraph.Adj` requires two
valid vertices whose addresses differ by one appended bit
([CoreGraph.lean:9](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/core/CoreGraph.lean:9)).
Thus internal unlabeled vertices are vertices of the graph being reviewed.
`ResidualAdj` literally removes both orientations of each recorded
`(p.dropLast,p)` original edge; `ResidualWalk.refl` requires `Valid`, and its
step constructor uses `ResidualAdj`
([OriginalGraph.lean:59](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/OriginalGraph.lean:59)).

The central exact statement is `region_component`:

```lean
ResidualWalk T cuts u v ↔ Valid T v ∧ Region cuts r v
```

Its premises are `r = [] ∨ r ∈ cuts`, `Valid T u`, and `Region cuts r u`;
there is no displayed-tree walk or payload assumption in this equivalence
([OriginalGraph.lean:191](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/OriginalGraph.lean:191)).
The proof uses `region_walk`, which walks the original address path one edge at a
time, and `residual_walk_prefix_same`, which prevents a walk from crossing a
recorded cut. `CutHistory.covers` partitions addresses into rooted regions;
`CutHistory.all_components` restricts that statement to every valid original
vertex; `CutHistory.rooted_components` separates distinct recorded roots
([Regions.lean:72](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Regions.lean:72)).

The exported `RealizedOutput` explicitly quantifies over every valid original
vertex, requires a representative root in the component list, separates those
roots, and requires every valid vertex to reach an original leaf
([Realization.lean:29](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Realization.lean:29)).
`History.finish_realizes` derives the final leaf-bearing clause from nonempty
component labels, their original-leaf witnesses, and residual walks; it does not
take the absence of leafless components as a premise
([Realization.lean:68](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Realization.lean:68)).
The list is literal output order: detached origins/labels followed by the
original-root component. Its roots are exactly `sourceCuts ++ [[]]`, without
repeated roots, and its label lists are exactly the output partition.

## Read: history and suppression

The `History` constructors accept the initial executable state, normalization,
or a selected nonroot group plus guards and the exact successful equation
`erase g.origin t = some next`
([History.lean:9](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/History.lean:9)).
They do not accept `Models`, an original-component correspondence, or an output
realization as inputs. `History.invariant` derives those intermediate facts from
the constructors under `(leaves T).Nodup`.

The detachment proof obtains a `GLeafErase` witness from
`erase_leaf_realization` using unique origins, then derives the payload
difference and updated display facts
([History.lean:44](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/History.lean:44),
[EraseLift.lean:40](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/integration/EraseLift.lean:40)).
`GLeafErase` deletes exactly the selected current leaf and suppresses its unary
parent; it does not equate a displayed edge with one original edge.
`Display.gleaf_models` rebases the surviving display while preserving exact
original-label membership at both the base and surviving root origin
([Display.lean:226](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Display.lean:226)).

`History.selected` derives that the selected origin is valid and live and its
labels are nonempty, valid original labels, and exactly its original live
descendant leaves
([History.lean:66](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/History.lean:66)).
`live_original_edge` then supplies the still-present original edge into that
origin, including validity of its original parent through `ResidualAdj`
([Regions.lean:108](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Regions.lean:108)).
`History.continuation_realizes` derives the selected component, nonempty
survivor, unchanged prior regions, and split of the old live region at the exact
continuation. `History.continuation_components` states the corresponding graph
component claims and separation from the original root
([History.lean:77](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/History.lean:77),
[Realization.lean:116](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Realization.lean:116)).

The production connection is named and noncircular:
`generate_finish_trace` → `run_finish_trace` → `step_finish_trace` →
`attempt_finish_trace` → a `History` ending with the literal finish output;
then `generate_original_realization` → `History.finish_realizes` →
`History.pair_components` → `component_of_region` → `region_component`.
The continuation hypothesis in `attempt_finish_trace` is discharged by induction
on `run` rather than assumed for `generate`
([History.lean:103](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/History.lean:103),
[Realization.lean:109](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Realization.lean:109)).

## Read: finite coverage

The exact original-label direction is:

```lean
def Refines (F Q : List (List Nat)) : Prop :=
  ∀ P, P ∈ F → ∃ R, R ∈ Q ∧ ∀ x, x ∈ P → x ∈ R
```

Consequently `Refines bs o.partition` preserves every input block inside an
output block; the generated partition may coarsen the input partition
([Composition.lean:4](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/geometry/Composition.lean:4)).
`Tracked` follows each original input block either into one detached payload or
into current groups with a common source owner. `tracked_normalize`,
`tracked_erase`, and `tracked_finish` preserve that direction
([Coverage.lean:6](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Coverage.lean:6)).

The finite induction measure is a literal list of current-leaf owner
representatives. `OwnerCover` requires actual current leaves and coverage of
every current-leaf owner; it requires neither a cardinality of owner IDs nor
distinct representatives
([OwnerCover.lean:103](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/OwnerCover.lean:103)).
`FullTransport` includes surjectivity onto new current leaves, so normalization
maps the list without increasing its length. At singleton erasure,
`erase_owner_cover` proves the selected current address occurs in the list and
filters that address out, so the next list is strictly shorter even when the
list contains duplicates
([OwnerCover.lean:36](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/OwnerCover.lean:36),
[OwnerCover.lean:132](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/OwnerCover.lean:132)).

The dependency premises are ordinary graph partitions. `SourcePartition`
contains actualness, terminal-owner equivalence, connected supports, and
disjoint supports, with no generator-coverage field
([CoreGraph.lean:185](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/core/CoreGraph.lean:185)).
`checkedSourcePartition` constructs these fields from the executable
`partitionCheck` and `pairwiseEmbeddings`; `initialPartition` carries them to the
group-color skeleton while keeping original addresses
([SourceBridge.lean:241](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/integration/SourceBridge.lean:241),
[InitialLift.lean:88](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/integration/InitialLift.lean:88)).
Normalization uses `homogeneous_cherry_coarsening`, `contractPartition`, and
the exact `normalize_gcontracts`. Suppression constructs survivor supports as
terminal hulls, with connectedness and disjointness proved using the old source
supports and path embedding
([CherryCoarsening.lean:196](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/core/CherryCoarsening.lean:196),
[Contraction.lean:135](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/integration/Contraction.lean:135),
[Normalization.lean:170](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/integration/Normalization.lean:170),
[Suppression.lean:191](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/integration/Suppression.lean:191)).

`run_refinement_coverage` assumes a reachable history, distinct original labels,
a monochromatic source partition, an owner cover, original-block tracking, and
`reps.length ≤ q + 1`. Its conclusion constructs an output at budget `q` and
the refinement relation
([Coverage.lean:89](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Coverage.lean:89)).
The zero-budget nonfinish cases contradict positive length of the next owner
cover. Successor cases use exact chooser singleton lemmas, the executable
`attempt_singleton_source`, strict list decrease, and `tracked_erase`.
`generate_refinement_coverage` constructs all of those initial hypotheses from
ordinary source checks and block monochromaticity, at any budget at least
`bs.length - 1`, including the generator's leaf-count cap
([InitialCoverage.lean:95](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/InitialCoverage.lean:95)).
No successful output is supplied as a premise in that theorem.

## Read: cost and output validity

`run 0` may inspect the normalized state and finish, but every attempted child
uses a continuation with no outputs. `run_zero_cost` therefore proves that any
zero-budget output retains exactly the existing cut list, and `run_cost_bound`
charges one original cut for each successor
([CoreProgram.lean:118](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/core/CoreProgram.lean:118),
[Cost.lean:174](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Cost.lean:174)).
`generate_cost_bound` bounds `o.sourceCuts.length` for every member of the
literal generated output list. `RealizedOutput` supplies
`o.partition.length = o.sourceCuts.length + 1`, so component count and cut count
are connected by an explicit equality, not by output-list cardinality
([Cost.lean:198](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Cost.lean:198),
[Realization.lean:41](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Realization.lean:41)).
The lower bound is `colorCount T color - 1 ≤ o.sourceCuts.length`, derived from
all original labels being covered, nonempty blocks, output monochromaticity,
and the component-count equality
([Cost.lean:114](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Cost.lean:114)).

`generate_payload_perm` proves that output flattening is a permutation of the
original leaves; `generate_partition_check` combines that statement with
original-label distinctness and block nonemptiness
([ValidPartition.lean:9](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/ValidPartition.lean:9)).
The final named call is `checked_source_core` → `source_core` →
`generate_refinement_coverage`, plus `generate_partition_check`,
`generate_monochromatic`, `generate_realized_color_cost`, and
`generate_cost_bound`
([ValidPartition.lean:52](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/ValidPartition.lean:52),
[Cost.lean:207](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/cut_realization/Cost.lean:207)).

## Inferred: review conclusion

The inspected proofs address the requested semantic risks without assuming the
desired generated output. Original-component claims cover unlabeled and
suppressed original vertices, and the leaf-bearing condition is derived for
every component. The history induction supplies the actual original-edge
witness and preserves prior components. Finite-budget coverage has the
original-block-to-output containment direction required by its interface, and
the proved cost bounds concern original cuts of an individual output. These
conclusions are semantic review inferences from the named source facts above;
they do not add a new theorem or an acceptance certificate.

The exported source-core signature does not assert raw output count or mass,
polynomial implementation work, two-tree restriction agreement, or complete
rooted-MAF algorithm composition. It also does not directly return the Boolean
`pairwiseEmbeddings T o.partition = true` or a residual component tree isomorphism
after suppression; it returns original-graph component realization and the
ordinary label partition checker. A consumer requiring those additional
statements must name and check its separate bridge. This report has not searched
for such bridges outside the allowed sources, and makes no claim that they are
absent elsewhere.

## Source hashes

Paths below are relative to `/Users/paurel/Documents/ChatGPT/bootscience`.
The hash names the complete file bytes even where the reading was selective.

| Source | SHA-256 |
| --- | --- |
| `research/rmaf/algorithm/universal233/cut_realization/OriginalGraph.lean` | `1f228db7d7df4cbe7d368747fbffef83641b6a52bc2629be350504bb7c322d88` |
| `research/rmaf/algorithm/universal233/cut_realization/Display.lean` | `bffcf3e3df26f7f2f5ce79959e303f21801b21731878492b5ef9c590c18f46dc` |
| `research/rmaf/algorithm/universal233/cut_realization/Regions.lean` | `88e4d4529b0e4555761ca6049999f484c102fcdbbb407207ad2b39e05a8fb0d5` |
| `research/rmaf/algorithm/universal233/cut_realization/History.lean` | `4f40af3a1275f6fbed2d1b017109399c188f61ccce50ca2319effec7868da577` |
| `research/rmaf/algorithm/universal233/cut_realization/Realization.lean` | `d440b98eeff7fd5955532d804063817f615fd92f3da5e0c049453af8f712bcb9` |
| `research/rmaf/algorithm/universal233/cut_realization/OwnerCover.lean` | `464604a8c2fdad1bca162367103b71b9cb2b866d0d8837a1de3ee28e43e79dbd` |
| `research/rmaf/algorithm/universal233/cut_realization/Coverage.lean` | `59df6e64beead296a71cb9b282432e03b4a883bc483d6dd1800645c6d2606556` |
| `research/rmaf/algorithm/universal233/cut_realization/InitialCoverage.lean` | `2b985c92c85b22d7b49a63a391b1add4e9e5a1bec622ce016d900a932a29c9b6` |
| `research/rmaf/algorithm/universal233/cut_realization/Cost.lean` | `88ac32b1fa6303353506f2edd26b30daab7a625940b762ce0c046990f2e0483b` |
| `research/rmaf/algorithm/universal233/cut_realization/ValidPartition.lean` | `b5543ebef7c5ba2d4d0fea8307a738acd74c4ac24e1ae43e514dee9345e37ded` |
| `research/rmaf/lean/RMAF.lean` | `4960d5be9a5f1eb6b15d11c76130bee5263125631314a4eb2d43d500d5b513a9` |
| `research/rmaf/algorithm/universal233/core/CoreGraph.lean` | `7099d4aa48a771f1d56e11bd36447a51d7e3c57094a6779c0d40acec11dca7a0` |
| `research/rmaf/algorithm/universal233/core/CherryCoarsening.lean` | `2f7142129ee2bc7bc188c629d1e6f225211278f5689dcb1dea38cc516247c0b8` |
| `research/rmaf/algorithm/universal233/core/CoreProgram.lean` | `9aa92355dfecf6e0e3d7707c1c284cabcb2f3846b6682e3b55b719e35cb7311f` |
| `research/rmaf/algorithm/universal233/core/CoreInvariants.lean` | `c4801fbfa04dcf83e9f79c91fe9e9834d0f7d030298a9e3ef1671c14de30ad19` |
| `research/rmaf/algorithm/universal233/integration/SourceBridge.lean` | `2eb4542a64461399029c6d3e0cb6dddd77d8b5b555d17e03abf8066a1cf7e93f` |
| `research/rmaf/algorithm/universal233/integration/Contraction.lean` | `956d7acadd05b9aba389d45e34699776999f745c063e9d5d66062e5816f3f8b4` |
| `research/rmaf/algorithm/universal233/integration/Normalization.lean` | `4dd4c1239d02e2452d94dcf254b7ca073c844428bbf07d3219dac3dc9e4b615c` |
| `research/rmaf/algorithm/universal233/integration/InitialLift.lean` | `2fb05bd9dfc20a7bfe9e128615ac3eb7b3ed0054fae63ca37d12c7bfb33fc811` |
| `research/rmaf/algorithm/universal233/integration/Suppression.lean` | `cf76359d9dff313237e2565aded7bff1c68fdb605690846d82145b5237bd978c` |
| `research/rmaf/algorithm/universal233/integration/EraseLift.lean` | `3a9a1df4eb4549fa44af20cd785e4fd183261b2b01227c12f5bda9e36473e5f1` |
| `research/rmaf/algorithm/universal233/integration/Origins.lean` | `43b33498a9a48f3434986d2e382ade610f60e3d4cbff60cbb461c25d60eefb23` |
| `research/rmaf/algorithm/universal233/integration/Branches.lean` | `638fffbede206252d81802ea6b14269e2a58ddae69653857c97c8bd17661dce3` |
| `research/rmaf/algorithm/universal233/integration/CutRecords.lean` | `6e14f512ff9304ded10766a26d2e9e9678ccc904c28a11cdc1bfddbb853a73a3` |
| `research/rmaf/algorithm/universal233/geometry/Geometry.lean` | `b98de754ee29fdeae54aebc6e03ffb7e8262dcb299f61b7ac5ca9bcee4887a9d` |
| `research/rmaf/algorithm/universal233/geometry/Bridge.lean` | `ba12f3b99d87efecce407dab54d95df003fc5e735cb12e314734c346317c9583` |
| `research/rmaf/algorithm/universal233/geometry/Composition.lean` | `097b9184ebacd913524fc3f0a130057004f95e30ba15f485adb9e0b7934578df` |

## Review limitations

No unverified background fact is used to support the review conclusion. The
source hashes establish file identity for this reading; they do not establish
kernel validity, numerical agreement, independence of the author proof design,
or replication. The parent review must assess its own rebuild and origin audit
evidence separately. Prose was reread for claim strength, locator accuracy,
scope, and the prose-lint clarity and honesty rules before delivery.
