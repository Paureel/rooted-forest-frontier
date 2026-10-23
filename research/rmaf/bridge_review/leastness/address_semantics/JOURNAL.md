# Tree address semantics

## Target

The module proves the pinned actual-vertex and selected-leaf-occurrence vocabulary for unchanged `RMAF.Tree`. It also derives unique occurrence addresses for each `RMAF.Instance` side. The target and `../INTERFACE.md` were read before proof construction; the initial skeleton was created in this directory.

## Provenance

The parent reported completion of its independent adversary-first pilot before assigning this proof. This author then froze `controls.json` and executed a separate local semantic pilot before writing `TreeAddresses.lean`. The local Python checks use an explicit stack and hand-written expected addresses; they import neither candidate Lean code nor extraction code. The author, inputs and mathematical address convention are shared with proof construction. These are development controls, and do not constitute a fresh nonauthor certification.

The module imports only `RMAF`, which imports `Std`. It uses no extraction, connectivity, prefix-hull or leastness result. Every node and leaf relation is defined inductively over the original `RMAF.Tree` constructors. No claim compares addresses belonging to different trees.

## Tool choice

I consulted `bootloops/tools/README.md` and the proof, tool-stewardship, provenance, acceptance, planted-truth and timing skills. The toolkit index has no package for binary-tree occurrence semantics. The existing `bootloops-lean` and `bootloops-python` wrappers provide the required runtimes; the local scripts only replay this problem's controls and compilation checks. No general toolkit capability is added or changed. The proof and replay files are confined to this directory; wrapper-managed job records are automatic.

## Frozen controls

The six fixtures cover a singleton root, empty selection, absent selection, repeated labels and selection, a deep selected pair, and a quartet crossing pair. Exact ordered ambient and terminal lists are pinned in `controls.json`. Five independently applied corruptions alter an ambient address, drop an occurrence, multiply terminals with repeated selection, insert an internal root as a terminal, and change a leaf label. Each corrupt candidate fails while its clean twin passes.

The first executed pilot, before candidate proof construction, reported:

```text
PASS: 6/6 exact semantic fixtures; 5/5 corruptions caught with clean twins.
```

Lean controls subsequently checked the frozen ambient and terminal values and all specified leaf occurrences. Positive examples also establish two distinct addresses for the repeated label 5 and reject an invalid ambient address. Three separate negative files falsely assert a missing repeated occurrence, invalid ambient membership and duplicate-selection multiplicity. Lean rejects each with `Tactic decide proved that the proposition ... is false`. The malformed-proof control is separate and fails with `Type mismatch`.

## Formal interface

`vertices` and `terminals` have the pinned recursive definitions. `ValidVertex.root`, `.left`, `.right` represent actual node occurrences. `LeafOccurrence.leaf`, `.left`, `.right` represent actual leaf occurrences. `mem_vertices_iff` and `mem_terminals_iff` establish both semantic membership equivalences.

`mem_leaves_iff_occurrence` establishes label membership if and only if an actual leaf occurrence exists. Every occurrence is valid (`LeafOccurrence.valid`) and its label belongs to `leaves` (`LeafOccurrence.mem_leaves`). `LeafOccurrence.label_unique` proves label functionality at a fixed address for arbitrary trees. `LeafOccurrence.address_unique` requires `(leaves t).Nodup`; repeated-label trees are allowed elsewhere.

The `instance_left_*` and `instance_right_*` results derive label membership, leaf-list nodup, occurrence existence and unique occurrence addresses from the unchanged permutation fields. `terminal_nonempty` takes an occurring selected label. The optional `vertices_nodup` and `terminals_nodup` results require no restriction on labels or selection multiplicity.

## Attempts

`attempts/TreeAddresses-01.lean` and `compile-01.log` preserve the first attempt. It failed because this `Std` environment does not expose the `by_contra` tactic. A `by_cases` proof replaced that tactic; no statement changed. `compile-02.log` records the core semantic interface, `compile-03.log` the uniqueness and Instance consequences, and `compile-04.log` the optional nodup results. Source snapshots before those extensions are retained. `CheckAPI.lean` and `attempts/api.log` retain the successful and unsuccessful standard-library name queries.

## Executed evidence

`audit_semantics.py` is the replay command's source. It rebuilds unchanged `research/rmaf/lean/RMAF.lean` and `TreeAddresses.lean` into the separate `replay-deps/`, then checks the declarations, frozen controls and rejection controls. Each subprocess has a 60-second timeout. The measured fresh RMAF compile took 5.65 seconds and the semantic module took 0.41 seconds in the initial replay; no unmeasured long computation was launched. `replay-receipt.json` retains exact measured durations, file hashes and run-specific logs.

The executed replay reported:

```text
PASS: fresh RMAF and TreeAddresses builds; standard-only axiom audit.
PASS: frozen fixtures in Python and Lean; 3 false semantic claims and malformed proof rejected.
Scope: address semantics only; fresh nonauthor acceptance remains with parent.
```

The source SHA256 is `f2bbd08201b98893a0e824f041e9af72761933d7f29b4e9a89088d9d9e46fdb0`. The unchanged RMAF SHA256 is `4960d5be9a5f1eb6b15d11c76130bee5263125631314a4eb2d43d500d5b513a9`. The source hashes are checked before and after replay. `AxiomAudit.lean` checks every theorem declaration in the semantic module; `replay-logs/axioms.log` contains only `propext`, `Quot.sound`, and `Classical.choice` among dependencies. There are no custom axioms, placeholders or `native_decide` calls in the module.

## Limits

This author has kernel-checked the semantic vocabulary and retained executable controls. The protocol status is CLOSED-UNVERIFIED until the parent obtains its fresh nonauthor review and consumer trace. The module does not prove extractor preservation or leastness, and no scientific runtime, novelty or cross-tree transport conclusion follows from this work. The full unrelated BootLoops package suite was not run; this module is checked through the fresh Lean builds and targeted semantic controls. The parent owns the aggregate theorem count.
