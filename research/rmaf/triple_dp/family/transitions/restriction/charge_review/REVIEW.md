# Independent review of the conditional charge route

The conditional count and cost statements passed this review. The review
found no blocking mathematical or interface error in the inspected charge
route. The result applies to the supplied Boolean selections and actual child
families under the hypotheses printed in `ChargeConsumer.lean`; it does not
construct restrictions of an arbitrary parent family or connect these Boolean
subtypes to a propositional `LiveIndex` model.

## Checked mathematical scope

`ChargeCore.lean:88` proves `count_balance` for a nodup complete parent
index enumeration covered by two Boolean predicates, with their intersection
confined to the optional parent index. Its count is by indices, so equal leaf
labels do not identify distinct indices. `close_balance` requires every
specified child-root owner to be selected; `four_charges` also retains the
continued parent's child-root ownership in the one-sided and merged cases.

`ChargeConsumer.lean:35` requires the literal list equation
`B.finite.elems.map Subtype.val = enum.elems.filter live`. Its conclusion
`B.cost = closedCharge enum.elems live (projectedRoot B)` follows from that
selection equation and the old family cost definition, not an assumed target
cost equation. The old definition is `FamilyAssembly.lean:78`:
`f.blockCount - boundaryCharge f.boundary`; `close_cost` removes the truncated
subtraction using the completeness of the finite enumeration.

`ChargeConsumer.lean:81` accepts actual `CostRoute.Family` children. The
hypotheses at lines 84–91 retain both selected-list equalities, both exact
support equivalences, coverage, overlap confined to the parent boundary,
and liveness of every occupied child root. The conclusions at lines 94–99
retain child-root support in the continued parent region. The root equivalence
at lines 59–75 proves the root correspondence from exact support; its reverse
direction also uses the stated root-liveness premise.
`conditional_family_count` at line 122 needs selection, coverage and overlap,
without assuming the requested count equation. These inputs are conditional;
none of these theorems produces a child family from a parent.

The target's geometric restriction, predicate identification and subtype
transport to `LiveIndex`, recovery by a support-preserving index bijection,
and transport through concrete normalized assemblies remain outside this
charge review. Full G2, legal color/mask states, executable correspondence,
algorithmic bounds and novelty are also outside its scope. This review read
none of the new restriction geometry, family restriction, count or recovery
proof bodies, and used none of the author checker or build implementations.

## Exact numerical evidence

The reviewer read the target first and created `REVIEW-SKELETON.md`. The
numeric protocol and implementation were then frozen in
`PRE-PROOF-FREEZE.sha256`, before reading the charge proof or checker bodies.
The evaluator traverses tree addresses, checks the family support conditions,
selects each child by contained leaf addresses, and sums exact index charges.
It was written from the semantic contract; no author implementation was reused.

| Required control | Fresh result |
| --- | --- |
| Eight positive fixtures | All expected fields exactly reproduced |
| Five numeric and three support/index corruptions | All rejected; all eight clean twins accepted |
| Four malformed families | Rejected for duplicate enumeration, omitted index, overlap, or wrong root owner |
| Raw leafless incursion | Valid parent family; left live indices `a,b`, right live index `o`; root liveness fails |
| Empty charge lists | Both tested empty-list charges equal zero |
| Numeric-blind copied source | All five numeric corruptions escape; the outer check rejects the copy |

The numeric report contains 22 result rows: 8 positives, 8 corruption/twin
pairs, 4 malformed inputs, 1 outside-premise case and 1 null case. R5 preserves
the parent-closed child-root owner and gives left cost 0. R6 leaves the unused
left root unowned and gives left cost 2. R8 preserves three parent indices
although all four leaf labels are equal. The mutated copy changes only the
integer comparison branch; the three structural corruptions remain rejected.
The source, copy, exact outputs and outer rejection are retained locally.

## Fresh Lean evidence

All thirteen source pins in the producer's final receipt matched before and
after the build. The reviewer copied source only into `fresh-lean-v1/`, which
initially contained no `.olean` files, and rebuilt the three older dependencies,
`ChargeCore`, `ChargeConsumer`, `ChargeControls`, `ConsumerSentinel` and
`ChargeQueries`. `LEAN_PATH` pointed only to this directory; the Lean executable
came through `bootloops-lean` and workspace `ELAN_HOME`. Its reported version
was Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

The reviewer separately queried the types and axiom sets of all twelve
requested declarations. `covered_balance` uses `propext, Quot.sound`;
`weight_eq_filter_length` and `projected_root_spec` use only `propext`;
the other nine use `propext, Classical.choice, Quot.sound`. The actual-family
`consumerT1` has the latter three standard axioms. No accepted queried theorem
reported a custom axiom, `sorryAx`, or a native-decide axiom. The source scan
also found no `axiom`, `sorry`, `admit`, `unsafe`, or `native_decide` declaration
in the inspected source files.

Each of the four original false-claim modules failed with Lean's diagnostic
that `decide` proved its proposition false. The reviewer generated a separate
corrected twin for each and compiled all four. The malformed import failed for
`NoSuchChargeModule`; it was classified separately and contributes no semantic
false-claim rejection. All diagnostics are retained in `lean-logs-v1/`.

The rebuilt actual-family T1 uses two leaves labelled 7. An additional reviewer
module applies the conditional count consumer to those actual families,
checks the exact support equivalences and distinct parent indices, and proves
parent count/cost `(2,2)`, child count/cost `(1,0)` on each side, and toll 2.
The producer's `consumerT1` invokes the conditional cost theorem with every
premise supplied. The additional module and its five axiom outputs are retained
as `ReviewerT1.lean` and `actual-T1-review-v1.json`.

## Provenance and limits

The author and reviewer share the frozen fixtures, target semantics, old family
definitions, Lean kernel and Std libraries. Independence here means separately
written numeric evaluation before proof inspection, plus fresh semantic review
and source rebuild; it does not mean a second independent proof formalization
or a different proof assistant kernel. Exact integers replace precision
escalation, and no fit or numerical recognition occurred.

The producer's final receipt hash is
`e953db51c351aa0522a6cc993c75b7e5b284ee6c13948fbd4a0ca59f5a073584`.
The pre-proof freeze hash is
`ca14755240ad2ef5ce106ed9edaa124cb8a8bcc40c7675fb358cc90ace2e5a33`.
The numeric evaluator hash is
`7c6027dc19447528f26e4f42e0ef3ffcc3afdf84c2cd1c02eef815a68134d3bb`.
The machine-readable review receipt retains the remaining source and output
hashes and links each claim to its evidence.

The broad `bootloops-check` suite was not run by this reviewer. No external
numerical engine was needed; the checked platform was macOS arm64. Producer
replay locking and its historical attempt narrative were not independently
inspected, because its driver/checker bodies were excluded. The retained
producer logs support the reported outcome of its eight-output comparator
mutation, while the fresh review uses the separate five-output numeric-blind
mutation described above. These limits do not weaken the stated conditional
Lean result, but they prevent treating this review as approval of the producer
checker implementation or of the complete restriction target.
