#!/bin/sh
# One-shot replay of the frozen path-route proof and controls. Each run retains
# separate dependency artifacts and logs; no frozen source or receipt is changed.
set -eu
PATH_ROUTE_WORKSPACE=$(CDPATH= cd -- "$(dirname -- "$0")/../../../../.." && pwd)
cd "$PATH_ROUTE_WORKSPACE"
PATH_ROUTE_SOURCE=research/rmaf/triple_dp/family/path_route
PATH_ROUTE_BUILD=$(mktemp -d "$PATH_ROUTE_SOURCE/build-replay.XXXXXX")
PATH_ROUTE_LOGS=$(mktemp -d research/rmaf/results/triple-family-path-replay.XXXXXX)
export LEAN_PATH="$PATH_ROUTE_BUILD"
shasum -a 256 -c "$PATH_ROUTE_SOURCE/FROZEN-WORK.sha256" > "$PATH_ROUTE_LOGS/freeze.log"
./bootloops-lean --version > "$PATH_ROUTE_LOGS/version.log"
./bootloops-lean -o "$PATH_ROUTE_BUILD/TripleDP.olean" research/rmaf/triple_dp/TripleDP.lean > "$PATH_ROUTE_LOGS/triple.log" 2>&1
./bootloops-lean -o "$PATH_ROUTE_BUILD/ConnectedRegions.olean" research/rmaf/triple_dp/ConnectedRegions.lean > "$PATH_ROUTE_LOGS/connected.log" 2>&1
./bootloops-lean -o "$PATH_ROUTE_BUILD/PathStem.olean" "$PATH_ROUTE_SOURCE/PathStem.lean" > "$PATH_ROUTE_LOGS/path.log" 2>&1
./bootloops-lean "$PATH_ROUTE_SOURCE/Controls.lean" > "$PATH_ROUTE_LOGS/controls.log" 2>&1
./bootloops-lean "$PATH_ROUTE_SOURCE/CleanChildWitness.lean" > "$PATH_ROUTE_LOGS/clean.log" 2>&1
PATH_ROUTE_WRONG_RC=0
./bootloops-lean "$PATH_ROUTE_SOURCE/WrongChildWitness.lean" > "$PATH_ROUTE_LOGS/wrong.log" 2>&1 || PATH_ROUTE_WRONG_RC=$?
if [ "$PATH_ROUTE_WRONG_RC" -eq 0 ]; then
  printf '%s\n' 'FAIL: deliberately false proposition compiled' >&2
  exit 1
fi
rg -q 'Tactic `decide` proved that the proposition' "$PATH_ROUTE_LOGS/wrong.log"
rg -q 'is false' "$PATH_ROUTE_LOGS/wrong.log"
if rg -n 'sorryAx|error:' "$PATH_ROUTE_LOGS/path.log" "$PATH_ROUTE_LOGS/controls.log" "$PATH_ROUTE_LOGS/clean.log"; then
  printf '%s\n' 'FAIL: accepted proof/control logs contain errors or sorryAx' >&2
  exit 1
fi
shasum -a 256 "$PATH_ROUTE_SOURCE/PathStem.lean" "$PATH_ROUTE_SOURCE/Controls.lean" "$PATH_ROUTE_SOURCE/CleanChildWitness.lean" "$PATH_ROUTE_SOURCE/WrongChildWitness.lean" "$PATH_ROUTE_SOURCE/replay.sh" research/rmaf/triple_dp/TripleDP.lean research/rmaf/triple_dp/ConnectedRegions.lean > "$PATH_ROUTE_LOGS/sources.sha256"
printf 'Lean proof accepted; seven concrete control theorem groups accepted; wrong proposition rejected with exit %s; matching clean twin accepted.\n' "$PATH_ROUTE_WRONG_RC" > "$PATH_ROUTE_LOGS/verdict.txt"
cat "$PATH_ROUTE_LOGS/verdict.txt"
printf 'logs=%s\nbuild=%s\n' "$PATH_ROUTE_LOGS" "$PATH_ROUTE_BUILD"
