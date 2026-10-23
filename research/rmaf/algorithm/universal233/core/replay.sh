#!/bin/sh
# One-shot source-bound replay for the colored source-core candidate.
set -eu
CORE_REPLAY_HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
CORE_REPLAY_ROOT=$(CDPATH= cd -- "$CORE_REPLAY_HERE/../../../../.." && pwd)
CORE_REPLAY_OUT="$CORE_REPLAY_HERE/replay/$(date -u +%Y%m%dT%H%M%SZ)"
mkdir -p "$CORE_REPLAY_OUT"
printf '%s\n' "$CORE_REPLAY_OUT" > "$CORE_REPLAY_HERE/LATEST-REPLAY.txt"
cp "$CORE_REPLAY_ROOT/research/rmaf/lean/RMAF.lean" "$CORE_REPLAY_OUT/RMAF.lean"
cp "$CORE_REPLAY_HERE/lean-toolchain" "$CORE_REPLAY_OUT/lean-toolchain"
for CORE_REPLAY_MODULE in CoreGraph CherryCoarsening CoreProgram CoreInvariants Audit FalseOneBranch FalseRootCut FalseExactPartition; do
  cp "$CORE_REPLAY_HERE/$CORE_REPLAY_MODULE.lean" "$CORE_REPLAY_OUT/$CORE_REPLAY_MODULE.lean"
  cmp "$CORE_REPLAY_HERE/$CORE_REPLAY_MODULE.lean" "$CORE_REPLAY_OUT/$CORE_REPLAY_MODULE.lean"
done
cmp "$CORE_REPLAY_ROOT/research/rmaf/lean/RMAF.lean" "$CORE_REPLAY_OUT/RMAF.lean"
shasum -a 256 "$CORE_REPLAY_OUT"/*.lean "$CORE_REPLAY_OUT/lean-toolchain" > "$CORE_REPLAY_OUT/SHA256SUMS.txt"
export LEAN_PATH="$CORE_REPLAY_OUT"
for CORE_REPLAY_MODULE in RMAF CoreGraph CherryCoarsening CoreProgram CoreInvariants Audit; do
  /usr/bin/time -p "$CORE_REPLAY_ROOT/bootloops-lean" -o "$CORE_REPLAY_OUT/$CORE_REPLAY_MODULE.olean" \
    "$CORE_REPLAY_OUT/$CORE_REPLAY_MODULE.lean" > "$CORE_REPLAY_OUT/$CORE_REPLAY_MODULE.log" 2>&1
  if rg -n 'error:|sorryAx' "$CORE_REPLAY_OUT/$CORE_REPLAY_MODULE.log"; then
    printf 'FAIL: compiler or axiom audit for %s\n' "$CORE_REPLAY_MODULE"
    exit 1
  fi
done
"$CORE_REPLAY_ROOT/bootloops-python" "$CORE_REPLAY_HERE/check_audit.py" "$CORE_REPLAY_OUT/Audit.log" > "$CORE_REPLAY_OUT/audit-check.log" 2>&1
for CORE_REPLAY_MODULE in FalseOneBranch FalseRootCut FalseExactPartition; do
  if "$CORE_REPLAY_ROOT/bootloops-lean" "$CORE_REPLAY_OUT/$CORE_REPLAY_MODULE.lean" > "$CORE_REPLAY_OUT/$CORE_REPLAY_MODULE.log" 2>&1; then
    printf 'FAIL: false proposition accepted: %s\n' "$CORE_REPLAY_MODULE"
    exit 1
  fi
  if ! rg -q 'is false' "$CORE_REPLAY_OUT/$CORE_REPLAY_MODULE.log"; then
    printf 'FAIL: false control rejected for an unexpected reason: %s\n' "$CORE_REPLAY_MODULE"
    exit 1
  fi
done
printf 'PASS: source-bound compilation, 112 complete axiom audits, 9 positive controls, 3 rejected false controls\n' > "$CORE_REPLAY_OUT/VERDICT.txt"
cat "$CORE_REPLAY_OUT/VERDICT.txt" "$CORE_REPLAY_OUT/audit-check.log"
printf 'Receipt directory: %s\n' "$CORE_REPLAY_OUT"
