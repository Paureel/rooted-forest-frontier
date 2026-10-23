# Pre-execution freeze receipt

Recorded UTC time from the clock tool: 2026-10-22 23:45:11 UTC (local date 2026-10-23).

Before either scientific control child was executed, `FREEZE-before-run-v1.sha256` was written from existing bytes of the own preregistration, own new script, pre-run report snapshot, screened target and unchanged wrapper/README. In particular:

- preregistration SHA256: `1c10c701f8113be75df6854f2d5abbbbfa6e55cd4b637142266f8550c2433dab`
- controls SHA256: `27ca50cc7f5308537aaa2f73b68074506b57902860cc65d51f3d7f8a5a7fffde`
- target SHA256: `42bca12c86286bd0ba0a747d28597f6f94aca2b1275044331d3f3ec943d71e96`

Exact command plan: `env BOOTLOOPS_MONITOR_DISABLE=1 ./bootloops-python` invokes the existing `run_capped.py` with fresh positive/corrupted run directories, labels `final-cold-cost-positive-v1` and `final-cold-cost-corrupted-v1`, the workspace cwd, no --seconds override, and literal child argv `./bootloops-python .../controls-v1.py positive|corrupted --result .../positive|corrupted.semantic-v1.json`. The corrupted run alone supplies wrapper `--want 23`.

No measurement or candidate contact preceded this freeze. No private resource receipt or prior calibration result was opened. The wrapper's own README was an expressly permitted contact; its prior-calibration descriptions are not used as executed evidence here.
