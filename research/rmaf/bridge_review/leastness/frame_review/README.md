# Leastness frame review

`referee_sim_REPORT.md` contains the human review. `receipt-verification.json` contains the source/log manifest and measured counts; `control-receipt.json` contains the five predeclared corruption outcomes. `audit-receipt.json` is the core bookkeeping result for `normalized-real-input.json`.

Reproduce the evidence bookkeeping from the repository root:

```
./bootloops-python research/rmaf/bridge_review/leastness/frame_review/bookkeeping_audit.py
./bootloops-python research/rmaf/bridge_review/leastness/frame_review/collect_receipts.py
./bootloops-python research/rmaf/bridge_review/leastness/frame_review/bookkeeping_audit.py research/rmaf/bridge_review/leastness/frame_review/normalized-real-input.json
```

The adapter pins the final reviewed documentation and the preserved original versions. Changed documentation requires a new review and deliberate pin update. Any mismatch in a source or log invalidates its receipt. These scripts check bookkeeping, declarations and diagnostic classes; they do not prove the mathematical claim or rerun the graph enumeration.

The nearest toolkit instrument, Emitall, was checked through `bootloops/tools/README.md` and `bootloops/tools/emitall/GUIDE.md`. It checks quoted numeric receipts but does not classify Lean declaration origins or compiler diagnostic semantics. These scripts therefore remain an explicitly one-shot project adapter rather than a second general-purpose toolkit package. Their synthetic records, literal source-parser controls and hash controls must pass before real comparisons run.

The Ruby renderer uses the installed RDoc library for a text-preservation check. Its output is not a GitHub table-layout preview. This review introduced no scientific evaluator and changed no upstream toolkit or proof source.
