# Persistent finite-bit standalone checker

The package proves a source-level correspondence for a standalone checker whose labels, budget, and intermediate counters are stored as Boolean lists. Production dispatch, native compiler semantics, and the complete rooted-MAF 2.33 runtime theorem remain open. The work field measures the displayed source cost model; its mathematical Nat bookkeeping does not establish native machine cost.

`PersistentEntry.lean:79` proves that `checkerFromInput` projects to the frozen `GenericForest.checked` for every supplied represented target, source list, budget, and candidate forest. `checkerCapacity_ready` at line 32 constructs every capacity premise by traversing those inputs. The checker handles malformed forests under the same correspondence; it does not assume that rejection occurs early.

`PersistentEntry.lean:94` proves the local bound

```
checker work <= setup work + 256*(W+1) * 908*(N+1)^6 + 4.
```

Here W is the length of the actual capacity returned by `checkerCapacity`. N bounds the projected target-node count, total source-node count, source-list length, candidate-block count, and total candidate cells. Setup executes target/source leaf copying, outer-list append, domain and forest traversals, bit-spine counters, and capacity widening. The theorem retains all of that setup work. `PersistentCapacity.lean:157` separately bounds the partition-capacity setup by the supplied bit-cell and payload sizes.

The executable value bodies do not call numerical encode/decode or the mathematical projection functions. `countLabel`, `lengthRegister`, subtraction, and budget comparison consume finite bits directly. `minimalLabels` preserves original unary address prefixes. Immutable label and address tails can be shared; explicit materializations and traversed list prefixes have returned work charges. The stored-reference audit resolves every custom name reachable from the 43 registered executable definitions; its remaining boundary contains 66 Lean standard primitive names.

The controls comprise eight positive groups with 22 exact assertions, nine false claims incompatible with their kernel-checked clean twins, six parser cases, and one forbidden-axiom module. The positive fixtures include source counts 386 and 378, empty and corrupted partitions, original unary addresses, budget rejection, and paid setup. An initial false-control reduction failure and the disk-floor compiler failure remain in the records and receive no acceptance credit.

The source theorem does not discharge the production caller obligation. Each actual recursive caller must use the represented state and invoke `checkerFromInput` at its checker sites, prove the displayed N premises, and add `checkerCapacity.work + 4` at every call. Conversion from a Nat-based production state, reuse or amortization of setup, and a logarithmic width bound for the complete solver require separate proofs. This author continuation used the existing source/compiler/audit lineage and receives zero independent verification credit. Main acceptance, base, novelty, and fresh review remain open.

Replay uses `./bootloops-python research/rmaf/algorithm/universal233/ordinary_dispatch/forest_binary_provider_binding/replay.py`. The replay creates a new result directory, reads the package, recompiles the 17 own source modules and identical controls, and reruns stored-body and forbidden-axiom audits. It rebuilds no frozen dependency and does not write the sealed source or compiled files.
