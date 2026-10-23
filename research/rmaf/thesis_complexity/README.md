# Independent Whidden thesis complexity reconstruction

The scientific status is **open**. The source's G4 credit analysis has a reachable local bound-substitution gap and a reachable state outside its declared |P|≤2 domain. Neither finding refutes the O(2^q n) runtime claim. See [report.md](report.md), [transition-ledger.md](transition-ledger.md), and [source-notes.md](source-notes.md).

Replay from the workspace root:

```sh
./bootloops-python research/rmaf/thesis_complexity/recurrence_audit.py
./bootloops-python research/rmaf/thesis_complexity/reachable_trace.py
./bootloops-python research/rmaf/thesis_complexity/three_credit_trace.py
./bootloops-lean research/rmaf/thesis_complexity/Credit.lean
./bootloops-lean research/rmaf/thesis_complexity/Trace.lean
./bootloops-lean research/rmaf/thesis_complexity/FalseCredit.lean
```

The last command must fail: it is the deliberate false-recurrence control. Accepted logs live at `research/rmaf/results/thesis-complexity-*.log`; repair logs explicitly carry `repair1`/`repair2` and are not accepted proofs. JSON receipts distinguish diagnostic abstract transitions from executed tree traces. The source PDF and frozen hand controls are preserved.

The one-shot Python scripts check exact credit arithmetic and finite tree traces. They are not full MAF solvers and do not decide the universal runtime claim. The Lean programs check arithmetic and the finite predicates encoded from the thesis; they do not establish that those predicates completely formalize the published algorithm. No correctness-arm or convention-transfer code was read or imported. A fresh author's source-to-model review is still required.

Finite reachability here means the full legal recursive-call tree used for the source upper bound; optional early-success short-circuit evaluation is not modeled. Every listed prefix is compatible with a sufficiently large nonnegative cut budget.
