# Author depth-one proof checkpoint

The source-bound replay at `replay/20261015T101515Z` accepted 39 positive source
modules and audited 2,041 declarations by actual module origin. The observed
axioms were `Classical.choice`, `Quot.sound`, and `propext`. Fresh nonauthor
reconstruction and interface review remain pending; all three main milestones
remain OPEN.

For arbitrary natural-number original labels, `pretest01 T S` first checks
label uniqueness and equality of the two label sets. On proper trees it tests
the zero-cut whole forest and every actual nonroot original source edge. For
edge `p`, the checked forest is literally
`[subtreeLabels S p, complement S p]`. The exact candidate count is `2n-1`,
where `n` is the number of source leaves.

`Optimality01.candidate_complete` quantifies over every literal original
agreement partition of cost at most one. Its two-block case uses
`Reconstruction01.source_two_split`: assign distinct colors to the two checked
source blocks, consume the completed source-core theorem at budget one, and
use output monochromaticity and original partition uniqueness to recover
exactly one original block as an original subtree. No agreement hypothesis on
the entire source tree under those colors is supplied. The generator occurs
only in the proof; the executable pretest enumerates original edges directly.

`Optimality01.found_globally_minimum` proves global minimum over all original
agreement partitions. `rejected_lower_bound` proves that rejection excludes
cost zero and one. `Witness01.found_original_minimum` additionally proves that
the returned literal forest is a `CutRealization.RealizedOutput` of its
nonredundant zero or one original source cut. That predicate covers every
actual original vertex and gives a leaf in every full residual component,
including components with suppressed vertices.

The registered tests passed before the universal proof: identical trees cost
zero; the existing different quartet pair costs one and returns original edge
`[false,true,true]`; the crossed balanced quartet is rejected and its original
exhaustive assignment solver reports minimum cost two; singleton cost zero;
absent and repeated labels refused; empty partition and root-edge selections
rejected. The tests also preserve the literal original parent of the edge on
the suppressed path. Four registered false propositions failed in Lean.
`ConsumerControls` then applied the universal original-graph and lower-bound
theorems to those fixtures.

The direct source-color supplement was pinned after the universal author proof.
It checks that the crossed two-color quartet has no budget-one output, has two
budget-two outputs, and that the two whole color blocks fail the source
embedding check. The first supplemental false-test draft had an ambiguous
namespace name. Its failure remains recorded; the repaired version rejected
the intended false one-cut proposition. These supplemental tests are author
development contacts, and their timing is recorded in their versioned pins.

The replay accepted a true arithmetic control and rejected a false one, then
rejected all four original registered false propositions and the repaired
supplemental false source-color proposition. Its inventory checker caught
a removed axiom record, a wrong module path, a wrong module origin, and a
private custom axiom in a foreign namespace. The source checks caught altered
source bytes and a mismatched expected pin. The replay retained the source
copies and logs for every build and audit invocation; their recorded elapsed
times sum to 25.561 seconds. The relevant supplied validation command,
`./bootloops-check emitall`, also passed. No toolkit package was changed, and
the full package suite was not rerun.

`RUNTIME.md` gives a conservative source-level time bound
`O(N⁴(b+1))`, or `O(M⁵)` in total input bit length. The exact candidate count,
original-address depth, same-shape recursive-call bound, and minimal-embedding
tree-visit bound are kernel-checked in `Runtime01`. The remaining
primitive-operation accounting is a mathematical source audit. Formal
compiled-machine cost semantics, independent certification, and the complete
algorithm are outside this checkpoint. No novelty claim is made.
