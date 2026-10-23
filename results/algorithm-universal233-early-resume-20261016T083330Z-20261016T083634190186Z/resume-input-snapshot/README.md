# Early selector structural work

Lean proves value correspondence and uniform polynomial bounds for the actual ordinary properness/pretest prefix, CherryBranching.select, Rule4.select, and both orientations of FastOrdinary.early. These bounds concern the explicit structural unit-source upper evaluators. Binary scalar implementations, compiler/runtime correspondence, the global recurrence, and full 2.33 algorithm acceptance remain open. This author's continuation has no independent acceptance credit.

All public names below have prefix `OrdinaryDispatch.EarlyLocalWork`. For every tree T and S, choose any natural N with `treeNodes T ≤ N` and `treeNodes S ≤ N`. No properness, successful selection, accepted payload, or budget hypothesis is needed for these bounds.

| Source result | Exact companion | Bound on `.work` | Public theorem |
|---|---|---|---|
| `DepthOne.proper T S` | `meterOrdinaryProper T S` | `128*(N+1)^2` | `meterOrdinaryProper_value`, `meterOrdinaryProper_bound` |
| `DepthOne.pretest01 T S` | `meterPretest T S` | `400000*(N+1)^6` | `meterPretest_value`, `meterPretest_bound` |
| `CherryBranching.select T S` | `meterSelect T S` | `2048*(N+1)^5` | `cherry_select_envelope` |
| `Rule4.select T S` | `meterRule4Select T S` | `262144*(N+1)^6` | `rule4_select_envelope` |
| `FastOrdinary.early T S` | `meterEarly T S` | `1048576*(N+1)^6` | `meterEarly_value`, `meterEarly_bound` |
| `front q T S` | `meterFront q T S` | `2097152*(N+1)^6` | `meterFront_value`, `meterFront_bound` |

The public primitive interface is in ERInterface.lean. Its `earlier_clear_primitive_envelopes` theorem bounds the sum of both cherry-selector orientations and both Rule4-selector orientations by `1048576*(N+1)^6`. Consumers may import ERInterface and reuse the primitive bodies; this package does not inspect or certify any Rule5 consumer.

The `front` result ends just before recursive branch construction. `front_found_solve` binds every found pretest branch to the frozen `FastOrdinary.solve` at arbitrary q. `front_rejected_binding` identifies the early-selection branch. The structural bound holds even for q larger than the reduced leaf count. `meterFront_resources` allows original size caps NT, NS and separate label/budget caps L, Q. `ScalarDomain T S q L Q` means that every input label is below `2^L` and q is at most Q; this domain is not used to derive the structural envelope.

Each `.value` is equal to the named source value. Work may exceed the source's short-circuit path: the companions retain full later priority scans, failed conjunction suffixes and both Rule4 orientations. A found prefix may also charge forest materialization when the budget test fails. These are explicitly charged upper evaluators rather than a native trace claim. SOURCE-SHEET-v1.md identifies the calls and their size premises.

The positive controls checked all seven failed quartet candidates, every best-tail size, the toy winner and work 24, both source orientations, malformed inputs, an empty selector with exact work 16, and q=1000 on a singleton. Ten deliberately false propositions were rejected with `is false` diagnostics. The audit rejected a changed source hash, a missing producer, a duplicate stored occurrence and a custom axiom. The audit retained all nonproof bodies, actual proof references and transitive axiom sets for 706 stored occurrences in twelve source modules. The axiom union is exactly `Classical.choice`, `Quot.sound`, and `propext`.

`AUDIT-CERTIFICATE-v1.json` in the receipt named by ACTIVE-v1.json contains the measured checks. FINAL-MANIFEST-v1.json in the parent directory pins the authoritative readonly source snapshots and evidence. The original ten development sources and all earlier failures remain preserved; replaying their source is a same-lineage check.

For a new local replay, choose a fresh relative result directory and set `EARLY_RESUME_RECEIPT` to that path. Run `./bootloops-python` on this directory's run.py with `prepare`, then with `ELPrimitives ELGeometry ELPretest ELPretestBounds ELCherry ELRule4Primitives ELRule4Guards ELRule4Raw ELEarly ELOuter ERInterface ERControls`. Run ERFalseControls through `run.run('ERFalseControls',1)` and audit.py with the same environment. Preparation copies exact dependency source/olean pairs and never recompiles dependencies. Each Lean process has a 60-second limit, a 3072-MiB Lean memory cap, a 3-GiB live disk floor and a 16-MiB output cap. Use a new directory; the sealed result directory is immutable.
