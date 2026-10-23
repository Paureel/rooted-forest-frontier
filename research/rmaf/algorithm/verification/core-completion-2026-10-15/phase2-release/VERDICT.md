# Frozen source-generator completion review

Verdict: **PASS, scoped source-core completion**. This nonauthor review found
no gap in original-cut realization, finite-budget original-label refinement
coverage, all-output cut bounds, or exact raw rational LIST mass, under the
explicit source-partition hypotheses below. Main **Algorithm, Correctness and
Smaller base remain OPEN**. Replication count added: **0**.

## Exact reviewed statement

Let T be the ordinary nonempty binary `RMAF.Tree`, with distinct original leaf
labels, and let color be any Nat-valued function. Let F be a literal partition
passing `partitionCheck (leaves T) F`, with vertex-disjoint minimal original
source embeddings (`pairwiseEmbeddings T F = true`) and monochromatic blocks.
For every ordinary cut budget q >= |F|-1, the actual
`CoreProgram.generate T color q` emits a Q with **F refining Q**: each original
block of F is contained in some Q block. Equality and reverse refinement are
not conclusions.

For every actual emitted output o, write d(o) = `o.sourceCuts.length` and let
r be the number of distinct colors of original leaves. The reviewed claims
give:

- `sourceCuts` is a list of distinct valid nonroot ORIGINAL edge addresses;
- deleting exactly `(p.dropLast,p)` for each recorded p gives all original
  residual components, including suppressed/unlabeled original vertices;
- every component contains an original leaf, its exact leaf set is the
  corresponding literal output block, and the component count is d(o)+1;
- the literal blocks pass `partitionCheck` and are monochromatic;
- r-1 <= d(o) <= min(q, |leaves T|-1).

For every **rational** c >= 2, including 2 and 233/100, the **raw emitted list**
satisfies

    sum_{o in raw outputs, with multiplicity} c^(-d(o)) <= c^(1-r).

The rational theorem is direct; this review does not infer it from a numerical
c=2 check. No theorem about arbitrary real c is accepted here.

## Source and kernel evidence

Root released exact manifests, independently rehashed here before source
contact:

- source manifest SHA-256:
  `a153e4e878c2cde3bea73f604a01a4955ca1b8fd94e8baa1bc02833934f32e33`;
  all 140 immutable files matched;
- cut manifest SHA-256:
  `61658da7b8868079dc471b82965da66e095beafbde509a726c5b930bed84a182`;
  all 164 immutable files matched;
- pre-candidate readiness v2 SHA-256:
  `03c850d43d84457f4245a233f5c03a87396e90d545e91231ef56c928e3fdb59f`;
  all 20 immutable snapshots matched.

Fresh isolated builds copied source only, with no copied `.olean`, and set
`LEAN_PATH` to each new build directory. All nonstandard imports are registered
by exact path/realpath/source SHA. The source package rebuilt 26 modules and
audited all 1,604 originating declarations; the cut package rebuilt 28 modules
and audited all 1,735. Enumeration uses module origins, so private constants,
equations, matchers and generated proof auxiliaries are included. Positive
source scans found no sorry/admit/native_decide/custom axiom, unsafe code,
extern, implemented_by or csimp replacement.

The joint stack contains 37 author source modules plus this review's consumer.
Its complete audit has 1,945 declarations; literal `#print axioms` was also run
for all 1,154 theorem declarations. The observed dependency union is exactly
`propext`, `Classical.choice`, `Quot.sound`, with no project custom axiom.
The runtime is Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; the executable, Std.olean and
Lean.olean hashes and standard prefix are retained in the final-audit receipt.
Compiler success alone was not treated as semantic acceptance.

## Copy-only composition

The two author packages have different flat modules named `Coverage`.
They were first rebuilt separately. In `joint-copy/` only:

1. cut `Coverage.lean` is copied byte-for-byte as `CutCoverage.lean`;
2. cut `InitialCoverage.lean` changes its first import from `Coverage` to
   `CutCoverage`;
3. every byte after that import line is unchanged. All theorem bodies,
   hypotheses and conclusions are unchanged; frozen author files are untouched.

The full mapped stack was rebuilt and audited. Exact reconciliation found one
additional originating-module adoption: the lazily generated
`Universal233.CoreProgram.generate.eq_1` belongs to `Entrypoint` in the source
build and `InitialCoverage` in the cut and joint builds. Its raw Lean Expr
type AND proof body are identical in all three builds, SHA-256
`684dc9ed45b85799911abcf2595c33c5d14ed5f6a9703e3da3232cc02f44f399`.
The complete inventory permits only that checked adoption and the documented
cut module/private-name mapping. Wrong public/private origins, a missing
private/generated record, and a forged axiom closure are all rejected by the
exact inventory controls.

`joint-copy/NonauthorConsumer.lean` is an independently written consuming call.
`distinctColorCounts` proves equality of the two packages' finite distinct-color
counts. `every_actual_output` connects actual original-cut realization,
partition validity, monochromaticity, color lower bound and actual generator
cap. `completed_source_consumer` obtains the finite-budget F-refines-Q witness
from `generate_partition_coverage_paid`, attaches those all-output facts to
that same member of the same output list, and invokes `generate_rawQ_mass`
on that list. It supplies no output, coverage oracle or cost premise.

## Semantic proof trace

The bounded cut semantics review is in `child-cut-semantics.md`, with complete
source hashes and named proof calls. Its source reading supports, and does not
replace, this review's fresh rebuild and executable controls.

`CoreGraph.Adj` is an actual one-edge adjacency between valid original
addresses. `ResidualAdj` removes both orientations of each original recorded
edge. `region_component`, `CutHistory.all_components`, and
`CutHistory.rooted_components` establish complete original-vertex components
and separation. The executable `History` constructors contain only initial,
normalization, and guarded successful `erase` steps. `History.invariant` derives
original validity, display/payload facts, exact detached regions, and cut
history. `History.selected` and `live_original_edge` derive the next selected
original edge witness. `History.finish_realizes` derives nonempty component
labels and leaf-bearing components; neither is a supplied coverage assumption.
`generate_original_realization` traces every actual emitted output to that
history. `generate_payload_perm` and `generate_partition_check` separately
account for every original label, not only set membership.

Both finite-budget routes construct the initial source partition from the
ordinary `partitionCheck`/`pairwiseEmbeddings` checks. `SourcePartition` has
actualness, terminal-owner equivalence and connected/disjoint supports, with
no field asserting generator coverage. Homogeneous normalization uses proved
coarsening and exact graph contraction; the transport is surjective on current
leaf occurrences. The finite owner cover may have duplicates. Mapping preserves
its length; erasing a selected singleton owner filters a list containing that
owner and strictly decreases length. At q=0 a nonfinish continuation has no
outputs and contradicts positivity of the next owner cover. Thus pruning is
never counted as a successful covered output. Original block-label containment
is transported in the F-to-Q direction.

For mass, `colorCount_normalize` preserves distinct colors. A one-choice step
can remove at most one color; a two-choice selected color is nonunique and
survives elsewhere, using distinct origins to obtain a distinct group witness.
Each continuation consumes one recorded cut. `scaledQMass_append` counts both
branch lists in full, so two choices cost a factor 2/c <= 1. The zero-budget
continuations contribute their literal empty lists. `generate_output_cap`
is proved for every actual list member before `scaledQMass_clear` removes the
offset; truncated Nat subtraction is not used to hide an over-budget output.
`rawQMass` is exactly `List.map` followed by `List.sum`, with an Int negative
exponent and no eraseDups operation. These facts feed the universal rational
`generate_rawQ_mass`, not an optimum/distance-recognition oracle.

## Frozen controls replayed after release

The independent breadth-first original-graph and pointer-tree instrument was
frozen before completion source contact. Actual newly compiled Lean JSON
readout matches all 12 literal generator receipts, including raw output order,
cuts, refusals, visited prefixes, attempted children and pruned counts. Every
actual output is checked in the independent original graph for all residual
vertices, nonempty leaves, cuts+1 components, exact original cut witnesses,
proper blocks, monochromaticity and cost bounds. Four partition/refinement
fixtures and four canonical-label fixtures match. Arbitrary distinct label 7
is distinguished from the separate canonical `Instance` label condition;
duplicate original labels are refused.

The six frozen graph fixtures and four frozen addendum cases also passed 118
literal Lean assertions. These include the retained two-edge original path
root -> [0] -> [0,1] after suppression, rejection of the forged direct edge,
and rejection of a leafless-root `RealizedOutput`. The addendum checks actual
generator membership for the unlabeled/mixed-color forgeries and clean twins.
Three invalid original cut witnesses are rejected by the independent graph.
This is a fixed small-fixture replay, not a census or a full solver benchmark.

Both exact raw mass fixtures match independent Fraction arithmetic. The actual
crossed list has two cost-two entries and mass 1/2 at c=2 and 20000/54289 at
c=233/100. The synthetic raw duplicate list keeps three cost-two entries,
cost sum 6, mass 3/4 and 30000/54289 respectively. Omitting its duplicate from
either cost or mass, demanding emitted minimum cost 3, accepting crossed q=1
outputs, equality coverage, or reverse refinement is caught.

The corrected rejection receipt v2 records seven explicit false propositions
rejected because Lean proves their literal propositions false, with clean
twins accepted. These include all four unchanged pre-contact templates and
duplicate cost/two rational mass omissions. A compiled private custom axiom is
detected both as a private axiom and through its private theorem's closure;
the clean private twin passes. Dropping a private audit row, changing a source
pin, and the five forged inventory records are caught.

## Retained failures and correction

`FAILURE-LEDGER.md` records all verifier startup/elaboration/audit failures and
their retained sources/logs. Two v1 rational false-control logs were initially
misclassified because the checker matched the word `false` inside a
reduction-stuck diagnostic. They are **inconclusive and not counted**. The v1
receipt is retained and superseded by `...-rejections-v2.json`. V2 uses
kernel-certified exact mass identities and fraction-to-mkRat identities, then
rejects the explicit wrong mkRat equality with the diagnostic “proved that the
proposition ... is false”. No frozen expectation or author theorem was changed.

## Independence and remaining scope

`CONTACT-LEDGER.md` discloses prior global guarded-certificate work and the
four permitted specification contacts. CoreProgram's pre-existing finite
controls were visible, so this is an independent implementation and source
review, not a blind holdout or new replication. The original-graph instrument
imports no author/global/other-verifier code; shared mathematical-model
assumptions remain explicit. One bounded fresh-context child performed cut
semantic reading only. No running author was messaged or steered. No live
core_work, whole_source_mass, assembly source, pair-case geometry/exchange or
main workfile was read. The separate integration review is not counted here.

The accepted interface is a source generator. It does not by itself certify
polynomial implementation work per prefix, a complete solver/state/scaffold
proof, a two-tree agreement test, output restriction isomorphism after
suppression, or any global running-time base. The exported source-core
signature also does not directly return the output Boolean
`pairwiseEmbeddings` theorem; a consumer needing that exact interface must
supply its checked bridge from original components. Every remaining global
acceptance milestone stays OPEN. No toolkit suite, broad census, novelty
claim or standalone thesis campaign was run in this review.
