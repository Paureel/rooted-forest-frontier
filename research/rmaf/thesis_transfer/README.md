# Thesis convention-transfer audit

This folder investigates whether Whidden's reported augmented rooted-SPR bound can be compared with ordinary no-rho rooted MAF. The provisional exact construction is in TRANSFER-PROOF.md; remaining source-theorem obligations are in SOURCE-AUDIT.md. No global improved algorithm or novelty claim is accepted here.

## Independent exact checks

`oracle.py` is a deliberately separate, one-task enumerator. It constructs explicit numbered vertices, uses BFS paths for minimal spans, suppresses unlabeled unary vertices to compare rooted restrictions, and enumerates set partitions. It imports no previous MAF solver or oracle. Its rho is the thesis's labelled unary root. It is suitable for tiny finite adversarial cases, not large instances.

`gadget_attack.py` adds the two fresh leaves in opposite orders and checks every feasible augmented agreement forest's erase map, as well as every ordinary forest's lift. The output counts are finite exact comparisons; they do not prove the universal reduction. Each script stops on the first failed exact assertion. The first script also rejects malformed trees/partitions. Controls were pinned in controls.json before implementation; gadget-spec.json was pinned before gadget tests.

Replay:

```sh
./bootloops-python research/rmaf/thesis_transfer/oracle.py --n 3 4 --out /tmp/thesis-transfer-oracle.json
./bootloops-python research/rmaf/thesis_transfer/gadget_attack.py --n 1 2 3 4 5 --out /tmp/thesis-transfer-gadget.json
./bootloops-python research/rmaf/thesis_transfer/source_scope_attack.py
./bootloops-python research/rmaf/thesis_transfer/audit_lean.py
```

Negative controls are retained: controls-corrupted.json changes a known optimum; `gadget_attack.py --n 1 --mutate` makes the two graft orders equal and must fail; audit_lean.py compiles a deliberately false same-order disagreement theorem and requires rejection. Logs and JSON receipts preserve both controls and measured timings.

## Formal scope

Transfer.lean proves 11 declarations over the existing RMAF semantic definitions. Its actual graph lemmas establish old-root inclusion for mixed spans, two-mixed-block overlap, and incompatibility of one block containing both added markers and old labels. Its optimum-shift theorem explicitly assumes the global partition maps. The full map theorem, equivalence of unary and sister-leaf rho encodings, and thesis algorithm are not formally established.

audit_lean.py rebuilds the shared RMAF import from its source into this folder, compiles the transfer file, audits all printed theorem axioms, and checks a false-claim control. A pass certifies those declarations only. Standard Lean axioms are enumerated in the receipt; no sorry, custom axioms, or native_decide occur in the accepted proof.

## Provenance and maintenance

These are one-task reference checks, not a replacement toolkit package. The toolkit capability index was consulted and has no rooted-AF partition/span instrument. No official toolkit code, integrity pin, or upstream verification script was edited. Shared with the existing formal route: the mathematical problem definition and RMAF.lean semantic layer, first read after independent controls. Shared between this folder's Python checks: its own oracle.py and Python runtime. No claim of wholly independent certification is made for checks within that shared lineage.
