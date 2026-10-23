# Frozen hard-parent / whole-source assembly review

Verdict: **PASS, scoped assembly consumer**. Fresh source-only kernel builds,
complete origin/axiom audits, unchanged pre-candidate controls against actual
execution, explicit false controls, and source-semantic/interface traces found
no gap in the four released obligations below. Main **Algorithm, Correctness,
Smaller base remain OPEN**. Added replication count: **0**.

## Accepted scope and hypotheses

1. **Source validity for every generated output.** For actual
   `CoreProgram.generate S color q` members, the ordinary source partition
   checker and `pairwiseEmbeddings S` both return true. This is derived from
   actual original residual components, not displayed edges or a supplied
   source-validity field. Original cuts are distinct valid nonroot edges, all
   residual components have original leaves, and cuts+1 equals component count.

2. **Original hard2 safety.** Given source distinct labels, actual original
   agreement `agreement T S F = true`, an actual original target cherry a,b,
   and `pendantOriginal S a b = [p,r]`, deleting those two original pendant
   edges produces the literal three nonempty original components. Their label
   lists are `subtreeLabels S p`, `subtreeLabels S r`, and the remaining source
   labels. Every F has singleton a, singleton b, or **F refining these parents**.
   A length-two pendant list chooses p,r from S,a,b before quantifying over F.
   These are directed child edges leaving the original a-to-b hull; an ancestor
   edge entering a below-root LCA is not an additional pendant edge. Labels
   above that LCA stay in the root component. Sibling order is handled explicitly.

3. **Actual whole-source covers.** With T/S distinct labels and source labels
   supported by T, actual original agreement F, a proper literal parent
   partition [A,B,C], F-refines-[A,B,C], q >= |F|-1, and the printed target
   nonlabel/geometry hypotheses, the actual clique, four-chain and count-two
   diagonal generator lists contain o with F-refines-o.partition and
   o.partition-refines-[A,B,C]. It is a proper original source forest, has
   actual original cut realization, costs at most q, and clears its requested
   original target vertices. The diagonal coverage requires B occupying both
   targets and exactly two actual B joint regions. The hard consumers derive
   the parent partition/refinement from hard2 safety in its third branch;
   those facts are not additional hard-parent premises.

4. **Exact raw rational list mass.** Parent residues modulo three give a
   distinct original input-color count equal to the sum of actual local
   counts. The base-four joint code is injective on the actual region values.
   Under the printed occupancy/count hypotheses, for every rational c>=2 the
   literal raw lists, with every repeated entry, have mass at most 3/c^4,
   4/c^4, and c^-3+c^-4 respectively. The two hard cuts are already charged
   by parent tags; no extra c^-2 factor occurs. Coverage and mass consume the
   **same actual literal color functions and output lists**.

These are source-forest/clearing claims. No conclusion that the emitted Q is
already an agreement forest of T and S is accepted; a frozen control explicitly
refutes that stronger statement.

## Exact released inputs and source evidence

All manifests and members were independently matched before source contact:

| Package | Manifest SHA-256 | Matched files |
| --- | --- | --- |
| assembly | c7fd11453b315ad94b13fc8f440837ebd4ac3e0f92697275dbfd3d90879949bf | 233 |
| whole_source_mass | b422a7fa142bf06669cc7abdce581a7e791a672494ec2db159ce5aad9e0d5fb0 | 225 |
| hard_parent_refinement | e8177aebdebc839587763ef731785002a8a08b5608530aabc6336177557cd337 | 38 source pins + 97 receipt files |
| assembly_completion | 6efd06c43f8d84538ab6a215329b4b30f62ed2cb039632c6dfe70009faf1d6cd | 283 |

The hard receipt-list SHA is
`325eb6c6712f4fbd7be3faccfb31675912db347ab08a25190d9b87c11690a6a9`.
The 45-file READY manifest and old 377-file core review also match unchanged.

Each package rebuilt independently from copied source, with no copied `.olean`
and clean LEAN_PATH. Exact source paths/realpaths/hashes and every nonstandard
import are registered. The four isolated full-origin counts reproduce the
author inventories: assembly 45 modules/2,117 declarations; mass 29/1,738;
hard-parent 26/1,630; completion 60/2,491. Every originating private constant,
generated equation/matcher/proof auxiliary and unused declaration is included.
All positive source builds passed on their first kernel execution.

The completion stack plus `NonauthorConsumer` has 2,563 originating declarations.
A second inventory using the environment's two constant maps matches every
name and originating module exactly. Literal `#print axioms` ran for all 1,614
theorem declarations. Positive source scans reject sorry/admit/native_decide,
custom axioms, unsafe/extern/implemented_by/csimp replacement. The observed
dependency union is exactly `propext`, `Classical.choice`, `Quot.sound`.
The positive false-control twin module was separately source-built and audited
over all 52 originating declarations, with the same permitted union.
Runtime executable/Std/Lean hashes, compiler version/prefix, source/olean/log
hashes and commands are retained. Compiler exit status alone was not treated
as a semantic verdict.

## Copy/import and list-order interfaces

Assembly records both upstream source stacks. Their 17 repeated module inputs
were deduplicated only after source/compiled-hash equality checks. The only
author source adapter is reproduced independently on copies: cut Coverage is
renamed CutCoverage, and InitialCoverage's first import changes to that name.
Every byte of every theorem body, hypothesis and conclusion is unchanged.
Completion's 45 assembly and 29 mass module sources match their isolated copies
byte-for-byte. Its 25 hard proof/dependency modules match too. The isolated hard
fixture module named Controls is not imported in completion; completion's
different Controls is the source-coverage fixture module. This explicit
basename collision does not stand in for a proof adapter.

No originating-name adoption differs among the four current isolated stacks.
Relative to the historical cut-only core build, the lazy generated
`Universal233.CoreProgram.generate.eq_1` belongs to Entrypoint rather than
InitialCoverage. Its exact raw Expr type AND proof body match the prior reviewed
fingerprint `684dc9ed45b85799911abcf2595c33c5d14ed5f6a9703e3da3232cc02f44f399`.

Numeric joint encoding matches the frozen reference exactly: 4*first+second.
The actual four-chain concatenation order is BC, B-joint, AC, AB; the frozen
reference order is AB, AC, B-joint, BC. Expectations were not edited. Each named
call's literal colors and raw outputs match exactly, and the macro concatenation
is checked in its actual order. `actual_four_reference_permutation` proves the
universal occurrence-preserving list permutation. Coverage's membership proof
and mass both use the author's same actual order, so this reference-order
permutation introduces no changed algorithm theorem. Hard-parent output order
is [pendant p, pendant r, root], while the independent graph displays canonical
components [root,p,r]; their exact original label partition matches.

## Semantic and nonauthor consuming traces

The bounded fresh-context `child-hard-semantics.md` gives source-located hard2
proof traces and hashes. It performs semantic reading only; this review owns
the separate executed builds, controls and complete origins.

`pendantOriginal` depends only on the unsuppressed source and a,b. Components
identifies the executable two-label hull with its actual original path, proves
the directed pendant characterization, cut-head antichain, complete/separated
original residual components and original-leaf-bearing condition. Endpoint
uses the actual target cherry and checked connected/disjoint supports to prove
literal singleton-a/singleton-b/common-block alternatives. Restriction preserves
the actual cherry under label-preserving isomorphism and sibling swaps;
PendantExclusion excludes every pendant subtree from a common a,b block.
Refinement then uses source embedding disjointness to prevent any other F block
crossing a named cut. Safety constructs `LiteralOriginalThree`, the executable
proper parent partition and the original F-to-parent alternative.

`SourceValidity.component_contains_minimal` proves every minimal source hull
lies in its original residual component. Complete component separation then
gives `components_pairwise_embeddings` and `generated_source_valid`. This is
the previously missing named source-checker bridge, rather than an extra
source-validity premise passed to coverage.

`OwnershipBase.parentGroups` takes actual F blocks, not synthetic ownership
objects. Actual target agreement supplies disjoint original target embeddings;
different residue groups cannot share a piece label. The clique/four ownership
cover therefore chooses one of three/four request combinations. The two-joint
case derives the shared B separator from actual joint regions. `Requests`
converts nonlabel target clearing to original-label monochromaticity, calls
the already reviewed actual source generator within q, and derives parent
containment and requested clearing for its emitted witness. No F, optimum or
distance-recognition oracle is an argument of the executable generator lists.

`WholeColors.taggedColor_cardinality` derives the exact original color count
from source-label coverage and disjoint parent residue supports. Empty parents
contribute zero, so WholeCall explicitly requires nonempty parents; the final
`partition_mass_interface` derives those facts from the actual partition checker.
`OriginalColors` derives local counts from original target regions and preserves
joint cardinality by the base-four code. `WholeMass` invokes the reviewed raw
rational generator mass for each actual whole-source call and adds the literal
lists with `rawQMass_append`. There is no output deduplication, same-parent
cut-set product, or extra hard2 discount.

`PaidAssembly.same_tagged_color` and `same_joint_color` are definitional
equalities of the two independently constructed functions. Its clique/four/
diagonal list covers attach `OutputWitness` to actual members of the same
WholeSourceMass lists used in mass. HardConsumer's `hard2_refinement_split`
directly consumes named source safety; endpoint branches stay literal singleton
disjuncts, and only the refinement branch invokes those list covers. HardPaid
adds the exact mass bound to that same cover/list, deriving mass-interface
facts from the produced parent checker.

This review's `NonauthorConsumer` independently compiles a uniform hard-clique
consumer selecting p,r before forall F,q and attaching exact raw mass without
assuming parent refinement or a generated witness. It also proves the list
permutation and consumes all nine frozen original-agreement examples through
the actual paid-cover theorems at rational 233/100. Actual label, agreement,
partition, geometry, joint-count and budget facts are kernel checked there.

## Executed frozen and false controls

Actual newly compiled JSON readout passes 123 exact comparisons: all nine
named color maps, local/global counts, raw ordered output/cut lists, regions,
joint pairs, original hard cuts, all 15 hard agreement classifications on
three sibling variants, hard refinement alternatives, root/selected-label
exceptions, proper-but-crossing source parents and clearing-with-false-final-
agreement. The diagonal q=3 boundary keeps its cost-three call and prunes its
cost-four call. No expectation was refreshed from author values.

The unchanged frozen mathematical driver was then replayed with exact actual
Lean output tables in place of its reference generator. Unknown calls fail;
there is no reference-model fallback. Only its physical HERE and result
destination changed in a documented copy. All 207 positive comparisons and
52 false/corruption catches pass, plus the separately frozen three-group/nine-
false addendum. There were 41 actual-output uses. Each named call has an actual
original agreement F lost when that call is omitted.

Raw costs remain [4,4,4], [4,4,4,4] and [3,4]. At c=2 their masses are 3/16,
1/4 and 3/16; at c=233/100 they are 300000000/2947295521,
400000000/2947295521 and 333000000/2947295521. Legal repeated outputs add their
cost/mass again; missing or duplicate call identities, malformed receipts,
omitted/forged costs and the false extra c^-2 inequalities are caught.

Fifteen new explicit false propositions are rejected by the diagnostic
“proved that the proposition ... is false”, with clean twins accepted.
They challenge omission of endpoint alternatives, reverse refinement,
clearing-implies-agreement, missing clique/four entries, unpaid diagonal
costs, extra hard cuts, omitted duplicates, a root third region, a selected
leaf falsely cleared, source crossing, q-pruning, and rational duplicate/extra-
discount masses. No reduction-stuck, import or syntax error is counted.

The own frozen Std/Lean-only clean/unused-public/unused-private/used-private
toy sources were copied and rebuilt. The clean private twin passes. The
unused custom axioms compile but are rejected by full origin/axiom inspection,
even though the unrelated theorem closures are empty. Missing private or
generated rows and wrong private/public originating modules are rejected by
the dual complete inventories. Planted axiom modules are outside all positive
package/consumer imports.

## Failures, independence and remaining work

`FAILURE-LEDGER.md` preserves the metadata duplicate-input startup rejection,
two incomplete fixture-import origin audits, and a cancelled quadratic
whole-environment deduplication in this reviewer's second inventory. The
corrected ledger filters to the reviewed modules first. No author proof or
frozen expectation was changed; no candidate mathematical counterexample was
found. Every successful gate has retained source-bound output, rather than
being inferred from process activity.

`CONTACT-ADDENDUM.md` records the exact released contacts and reused own frozen
compiler/graph/driver primitives. One bounded child read the hard semantics;
no author was messaged or steered. No live restriction_bridge, rank_dichotomy,
pair_assembly, current main/work proof, or other reviewer was contacted. All
45 preparation and 377 earlier review files remain unchanged. Shared model
and checker lineage is explicit; this is not a blind holdout or a replication.

The next named consumer is the actual recursive `SolveForest(T,Q,q-d)` action,
endpoint branch consumption, source priorities/history and complete state/
termination/work accounting. They are outside this freeze and remain OPEN.
The present scopes do not prove Q's target agreement, a total recursive solver,
all local-query costs, a global recurrence/base, machine runtime, or novelty.
All three main milestones remain OPEN.
