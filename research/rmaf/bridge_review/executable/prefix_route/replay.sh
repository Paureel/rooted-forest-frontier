#!/bin/sh
# One-shot replay of the independent prefix-route receipt.
set -eu
PREFIX_ROUTE_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PREFIX_ROUTE_ROOT=$(CDPATH= cd -- "$PREFIX_ROUTE_DIR/../../../../.." && pwd)
cd "$PREFIX_ROUTE_ROOT"
mkdir -p "$PREFIX_ROUTE_DIR/build"
export LEAN_PATH="$PREFIX_ROUTE_DIR/build"
/usr/bin/time -p ./bootloops-lean -o "$PREFIX_ROUTE_DIR/build/RMAF.olean" research/rmaf/lean/RMAF.lean > "$PREFIX_ROUTE_DIR/rmaf-build.log" 2>&1
/usr/bin/time -p ./bootloops-lean -o "$PREFIX_ROUTE_DIR/build/PureBridge.olean" research/rmaf/pure_bridge/lean/PureBridge.lean > "$PREFIX_ROUTE_DIR/purebridge-build.log" 2>&1
/usr/bin/time -p ./bootloops-lean -o "$PREFIX_ROUTE_DIR/build/GraphRegion.olean" research/rmaf/bridge_review/lean/GraphRegion.lean > "$PREFIX_ROUTE_DIR/graphregion-build.log" 2>&1
./bootloops-python "$PREFIX_ROUTE_DIR/prefix_check.py" --max-leaves 4
/usr/bin/time -p ./bootloops-lean "$PREFIX_ROUTE_DIR/Finite4.lean" > "$PREFIX_ROUTE_DIR/finite4-build.log" 2>&1
/usr/bin/time -p ./bootloops-lean -o "$PREFIX_ROUTE_DIR/build/PrefixHull.olean" "$PREFIX_ROUTE_DIR/PrefixHull.lean" > "$PREFIX_ROUTE_DIR/prefixhull-build.log" 2>&1
if /usr/bin/time -p ./bootloops-lean "$PREFIX_ROUTE_DIR/NegativeControls.lean" > "$PREFIX_ROUTE_DIR/negative-build.log" 2>&1; then
  printf '%s\n' 'FAIL: intentionally false control compiled'
  exit 1
fi
./bootloops-python - "$PREFIX_ROUTE_DIR/negative-build.log" <<'PY'
import pathlib
import sys
s = pathlib.Path(sys.argv[1]).read_text()
assert s.count('Tactic `decide` proved that the proposition') == 2, s
assert s.count('is false') == 2, s
print('Expected two false-proposition failures recovered.')
PY
printf '%s\n' 'Replayed 816 comparisons, 9 exact controls, 4 rejected corruptions, prefix-hull proof, and 2 expected compiler failures.'
