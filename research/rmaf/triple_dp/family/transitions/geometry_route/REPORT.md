# Geometric support route — kernel checked, fresh review pending

This independently authored supporting route proves the geometric support
lemmas needed for the proposed merge. It does **not** construct the merged
finite family or prove its count/cost equations. Universal family merge and
full G2 remain OPEN from this arm. Protocol grade for these supporting
statements only: CLOSED-UNVERIFIED (fresh nonauthor review pending).

## Reusable interface

All declarations live in `TripleDP.GeometryRoute`.

* `jointSupport s t` is definitionally `True` at `[]`, `s a` at `false :: a`,
  and `t a` at `true :: a` (`GeometrySupportDefs.lean:9`).
* `jointSupport_root`, `jointSupport_left`, `jointSupport_right` give exact
  root and branch membership (`MergeGeometry.lean:10`, `:13`, `:16`).
* `jointSupport_union` gives the exact required interface:
  `jointSupport s t a ↔ a = [] ∨ liftSupport false s a ∨ liftSupport true t a`
  (`MergeGeometry.lean:20`).
* `jointSupport_prefixClosed` and `jointSupport_convex` prove convexity from
  prefix closure, respectively from child convexity and both child roots
  (`MergeGeometry.lean:28`, `:44`).
* `jointSupport_rootPaths` identifies the support with all prefixes of
  left/right lifted support addresses, assuming prefix closure and a left
  root witness (`MergeGeometry.lean:57`). Either child boundary supplies the
  required witness in the intended application.
* `jointSupport_bounded` uses the actual `CostRoute.Vertex` for
  `BTree.node l r` (`MergeGeometry.lean:74`).
* `jointSupport_labels` gives exact existential `LeafAt` label union
  without requiring distinct label values (`MergeGeometry.lean:85`).
* `jointSupport_disjoint_left/right` transport original child-support
  disjointness to disjointness from the entire joint support
  (`MergeGeometry.lean:101`, `:111`).

The family-facing abbreviation is `familyJoint f g i j` at line 122.
`familyJoint_convex f g i j hi hj` requires precisely
`hi : f.boundary = some i` and `hj : g.boundary = some j`.
`familyJoint_bounded`, `familyJoint_labels`, and `familyJoint_labelled`
provide actual parent vertices, exact `f.hasLabel i x ∨ g.hasLabel j x`,
and existence of a parent leaf in the merged support. These latter three do
not need boundary assumptions. `familyJoint_disjoint_left f g i k j hik`
requires `hik : i ≠ k`; the right version requires `j ≠ k`. They use the
original family's `disjoint` field (`MergeGeometry.lean:125–153`).

Consuming interfaces still missing from this arm: enumeration/reindexing of
survivors, all family coverage/root fields under those indices, survivor
pairwise disjointness as an indexed family theorem, count/cost equations,
and a concrete `Family` constructor. The existing lifted-support and label
lemmas in shared `FamilyAssembly` remain available to that constructor.

## Executed evidence

Final receipt (absolute):
`/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/results/triple-family-transitions-geometry-20261014T141457397535Z`.

It includes sources, per-source SHA-256, exact commands, timings, logs,
oleans, `axiom-audit.json`, and `PASS.json`. Lean is 4.35.0 on
arm64-apple-darwin24.6.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

The run rebuilt `TripleDP`, `ConnectedRegions`, and `FamilyAssembly` into a
new isolated `LEAN_PATH`, then rebuilt definitions and 7/7 positive
examples. The 2/2 deliberately false theorem files failed specifically with
`Tactic `decide` proved that the proposition ... is false`; their exact
correct twins compiled. Frozen controls were executed successfully before
universal proof writing in receipt
`triple-family-transitions-geometry-20261014T141117591066Z`.

All 17 theorem axiom queries completed. The union of queried axioms is
`{propext, Quot.sound}`. None uses `sorryAx`, `native_decide`, or custom
axioms. The vertex, label-union, leaf-existence, and disjointness statements
are axiom-free. Compiler failure outputs that mention `sorryAx` belong only
to the explicitly retained failed development build, not the final module.

Retained failures:

1. `triple-family-transitions-geometry-20261014T141016138602Z`: positive
   controls initially lacked automatic `Decidable` synthesis for opaque
   predicates. Explicit unfolding fixed elaboration without changing any
   frozen proposition or expected polarity.
2. `triple-family-transitions-geometry-20261014T141249894103Z`: the first
   universal proof build reused a local proof name and passed the original
   cons-prefix hypothesis instead of its tail. Naming the tail hypothesis
   separately fixed the source. This failed source and full axiom diagnostics
   remain in the receipt.

Earlier successful proof receipt:
`triple-family-transitions-geometry-20261014T141344761775Z`.
The final run added an executable axiom allowlist/query-count gate and
source hash emission during compilation; the Lean theorem source is the
same as in the earlier success.

## Replay and independence limits

From the workspace root:

```sh
ELAN_HOME="$PWD/.runtime/elan" ./bootloops-python research/rmaf/triple_dp/family/transitions/geometry_route/run.py --proof
```

The driver invokes `./bootloops-lean`, sets `ELAN_HOME` to the workspace's
runtime, and sets `LEAN_PATH` to the fresh receipt's `olean` directory.
It creates a new timestamped receipt without altering prior receipts.
Omit `--proof` to replay only the frozen controls and dependency builds.

No new main transition source or other new prover arm was read. This route
uses first-edge decomposition, prefix closure, and a root-path union; it
contains no finite-index deletion arithmetic. Shared layers with other arms
are the frozen target/controls, Lean/Std, and the audited old semantic
modules. Those shared layers mean this is forced-diverse authorship, not a
fresh verification of shared semantics. The parent supplied the X0 NO-FIRE
192-pair result; this arm did not rerun or inspect its checker.

Controls influenced this construction and are explicitly not held-out
certification. No fresh-author checker or interface review was performed by
this author. The general BootLoops validation suite was not run because
this change adds only local Lean proofs and a receipt wrapper; scoped Lean
rebuilds and axiom/control checks were executed instead. No upstream proof,
validation script, frozen protocol, or integrity pin was edited.
