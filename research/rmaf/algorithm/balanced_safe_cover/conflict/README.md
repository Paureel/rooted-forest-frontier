# GLOBAL-C: global conflict and separator route

`PROOF.md` gives the handwritten original-edge conflict characterization, a safe incidence-column reduction, a special matched-sector separator theorem, and the precise open unrestricted generation theorem. `ConflictPacking.lean` proves generic packing, substitution, and charged half-budget constituents. Source-tree correspondence and fresh nonauthor review remain pending. No new unrestricted exponential base or novelty is claimed.

The one-shot scripts remain here because they test this specific safe-cover research route. They do not extend the general BootLoops toolkit. Toolkit consultation, oracle contacts, source lineage, protocol revisions and failure logs are recorded in `SPEC.md`, its v2/v3 addenda, and `JOURNAL.md`.

| File | Use | Output meaning | Check required |
|---|---|---|---|
| `exact_conflicts.py` | Exact finite tests of original source-edge conflict semantics; cutsets and leaf partitions | Optimum, disjoint packing, survival and local distances for finite supplied inputs; its oracles are excluded from proposed algorithms | `controls-v1.json`, comparator mutations, and fresh nonauthor source/model rebuild before certification |
| `dominance_checks.py` | Finite regression for incidence-maximal original-edge candidates | Exact finite optimum preservation; shared author/code prevents independent certification | Four abstract controls and deliberate invalid domination, plus n<=4 pair comparisons |
| `mixed_cherry_family.py` | Test matched mixed-cherry sectors | Finite special-cover optimum and accounting checks; C6 proof remains handwritten | Sharp m1 exclusion, m2 clean twin, expected m>=2 values, mutations, fresh source review |
| `matched_sector_solver.py` | Exact polynomial special-family recognizer, budget decision and original-label witness reconstruction | `NOT_APPLICABLE`, exact budget failure, or optimum source-cut receipt; calls no optimizer/oracle | Budget twins, outside-family case, m1 exception, and polynomial agreement-witness validation |

Replay with workspace runtimes:

```sh
./bootloops-python research/rmaf/algorithm/balanced_safe_cover/conflict/exact_conflicts.py --controls research/rmaf/algorithm/balanced_safe_cover/conflict/controls-v1.json --output /tmp/global-c-controls.json
./bootloops-lean research/rmaf/algorithm/balanced_safe_cover/conflict/ConflictPacking.lean
```

`FalsePackingControl.lean` must fail and is excluded from production. `ConflictPacking-pre-control-fix-v1.lean` preserves an unsuccessful positive-control proof attempt; its failure log must remain available. Production axiom audits contain only Lean's standard propext, Classical.choice and Quot.sound where listed. No custom axiom, sorry/admit or native_decide occurs in production.

The complete n<=5 conflict census has 11,261 ordered pairs and 2,836,949 original source cutsets, with no characterization mismatch. Its finite scope and shared tree primitives are explicit in the receipt. Four leaves already separate packing=1 from optimum=2; six leaves separate packing=1 from optimum=3. Neither obstruction disproves safe-cover existence.
