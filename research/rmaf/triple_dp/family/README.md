# Labelled-family proof instruments

This continuation proves and checks normal forms for labelled disjoint regions
on a finite rooted binary tree. Use it for the family-level G2 interface; the
neighboring triple-DP instrument performs optimization and does not expose raw
support regions. `REPORT.md` states the current proof and remaining links.

Run the isolated Lean replay from the workspace root with an unused receipt:

```sh
./bootloops-python research/rmaf/triple_dp/family/audit_family.py --transport --receipt triple-family-lean-replay-2.json
```

The replay succeeds only if accepted sources build without proof placeholders,
all audited axioms are allowed, the concrete clean controls compile, and the
false closing-cost proposition fails for mathematical falsity. A PASS verifies
the listed Lean declarations, not full G2 or executable graph correspondence.
Original receipts are never overwritten. `archive/audit_family.v1.py` preserves
the initial auditor and `archive/audit_family.geometry-v1.py` preserves the
exact auditor hash used by the geometry receipt. Omitting `--transport` and
using `--geometry` replays only the earlier geometry layer; omitting both
options replays the original normalization layer.

The frozen direct-path controls ran through `check_controls.py`; its original
pilot/full outputs are retained and the runner refuses to overwrite them.
The raw/retained amendment receipt states its inline command provenance. The
independent adversary, path route, cost route, and fresh review have their own
subdirectories and receipts. Known examples are regression evidence. No large
census or runtime claim substitutes for the universal normalization theorem.
