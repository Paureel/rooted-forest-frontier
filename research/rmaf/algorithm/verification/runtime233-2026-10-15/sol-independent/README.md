# Precontact runtime calibration

This one-shot instrument calibrates a later counting/interface review. It reads the frozen hand-authored CONTROLS-v1.json through its normal JSON entry point and records exact Python arithmetic, clean twins, deliberate corruption catches, and source-bound Lean receipts. It never reads candidate or reviewer evidence.

Use `./bootloops-python research/rmaf/algorithm/verification/runtime233-2026-10-15/sol-independent/run_controls.py --pilot` for the tiny literal-trace pilot; omit `--pilot` for the fixed full battery. Every subprocess has an initial 60-second cap, Lean has a 1024 MiB limit, and at least 3 GiB free disk is required before each process. Logs are gzip-compressed and bounded. Failures remain as timestamped receipts; the runner never overwrites an earlier run.

Work units are abstract nonnegative integer costs, not measured machine time. Budget/size progress is lexicographic: budget strictly decreases, or budget is unchanged and size strictly decreases. Physical call IDs distinguish repeated executions even when state keys coincide. A positive record means the literal hand-specified answer was recovered. A corruption record means the altered claim was rejected at the intended comparison. Neither is candidate acceptance.

Before trusting a run, require all 12 Python clean cases, all 17 corruption catches, all 12 Lean positive theorem axiom reports, all 3 independently rejected false Lean files, frozen input/source hashes, and retained diagnostics. These controls are authored by this reviewer and do not constitute independent certification of this reviewer's constructions. Global runtime and mathematical acceptance remain OPEN pending the exact root release and subsequent source/interface reconstruction.
