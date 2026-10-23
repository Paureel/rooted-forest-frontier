# BootLoops workspace dashboard

A local, read-only companion to the toolkit: live process activity, recorded
runs, a source-linked map of 50 tools and 12 protocols, and an interactive
illustration while the workspace is idle.

## Start

From `/Users/paurel/Documents/ChatGPT/bootscience`:

```sh
./bootloops-dashboard
```

Open [the dashboard](http://127.0.0.1:8765). The server binds only to
`127.0.0.1`; nothing is uploaded or published. Stop the server with Ctrl+C.
Use `--port 8766` for another port, or `--no-discovery` to show only explicitly
recorded jobs. There are no HTTP commands to launch, stop, or modify jobs.

## Record work

The existing workspace launchers now record automatically:

```sh
./bootloops-python your_script.py
./bootloops-check mixalot eras
BOOTLOOPS_RUN_TITLE='My calculation' ./bootloops-python your_script.py
```

The child retains stdin, separate stdout/stderr, and its exit status. Python
REPL sessions and `-i` retain their original terminal behavior. For an
uninstrumented invocation, set `BOOTLOOPS_MONITOR_DISABLE=1`.

The dashboard can also discover Python and Julia commands whose script lives
inside this workspace, or whose command identifies a BootLoops tool. An
inherited working directory alone is insufficient: unrelated plugin servers
are excluded. Directly observed jobs provide resources and process identity,
but no captured output or known exit code. Very short unrecorded processes can
fall between one-second samples. Use the launchers for reliable history.

## Report internal work

Internal scientific stages are optional, explicit telemetry. The dashboard
does not infer acceptance from CPU, a success exit code, or arbitrary log text.
After `source ./activate.sh`, this module is on the Python path:

```python
from telemetry import step, metric, gate, artifact

with step('compute', tool='nestor'):
    # Run the actual calculation here.
    metric('completed', 12, total=20, unit='points')
    metric('digits', 60, unit='working digits')

# Emit only after executing and saving the actual check.
# gate('independent', 'passed', detail='Comparison receipt: results/check.json')
# artifact('results/check.json')
```

Stages: `input`, `structure`, `compute`, `check`, `result`.
Checks: `known_truth`, `independent`, `precision`, `unused`.
Check states: `passed`, `failed`, `skipped`. A check is a **reported claim**,
not independent certification by the dashboard. Absent checks stay gray and
unreported. No prediction-improvement metric is used as an acceptance gate.

## Reading the views

- **Flow**: explicitly reported stages, plus the observed start/end of the
  process. A completed process is not a verified scientific answer.
- **Toolkit**: nine navigation groups organized by purpose. Dots open tools;
  group centers open the capability’s list. Groups and connecting lines are
  conceptual, not mandatory dependencies. The second layer contains all 12
  installed protocols. Explanations carry the original index row and locator,
  with the tool guide available on demand.
- **Activity**: CPU and summed resident memory of the job and its children.
  CPU uses one core as 100%, so multiple cores can exceed 100%. Resource
  charts retain the latest 240 samples; recorded peaks cover the whole run.
  A resource sample can be partial if a process exits or cannot be read.
  The optional completed-output count is progress; CPU is activity.
- **Runs**: recorded outputs, exit status, tools, reported checks, resources,
  and artifacts survive reloads and server restarts. The installation entry
  is explicitly imported from the combined installation validation record;
  it is not one uninterrupted run or acceptance of a scientific result.
- **Demo**: a synthetic walkthrough of numerical integration, error enclosures,
  independent checks, and exact-form recognition. Play, pause, choose a stage,
  or vary target digits. The drawn intervals and green checks are illustrative;
  the demo launches no process and certifies no digits.

The screen shows short labels. Definitions, sources, guides, and detailed
output appear only when opened. The interface switches to live activity when
a recorded run starts and back to the demonstration when the workspace is idle.
An explicitly selected Demo or historical run remains selected.

## Proof campaigns

Open `http://127.0.0.1:8765/#proof` for the rooted-MAF campaign. Its stream
updates local checkpoints every second. Routes, colored forest components,
lemma nodes and historical checkpoints open their evidence in the drawer.
Selecting a component highlights its minimal embedding in both trees.

`research/rmaf/spec.json` pins the conventions, target and acceptance gate.
Each research route atomically updates its own JSON under `progress/` with
`id`, `title`, `status`, `summary`, `metrics`, `claims`, `lemmas`, `artifacts`
and optional `sources` and tree `example`. The dashboard preserves observed
revisions in `.dashboard/proofs/rmaf.jsonl`. An open claim remains open after
a successful process exit. Source checks, finite tests and Lean proofs carry
their scope in the details. Counts include the formal library and auxiliary
audit without counting their duplicate graph nodes.

Lean is pinned to 4.35.0 under `.runtime/elan`. Source `activate.sh` for
`lean`/`lake`, or use `bootloops-lean`/`bootloops-lake` for recorded commands.
The formal project and replay/audit evidence live in `research/rmaf/lean/`;
auxiliary proofs are replayed by `./bootloops-python research/rmaf/audit_routes.py`.
Intentional false-proof controls are excluded from production builds.

The read-only `/api/proof/file` preview permits text evidence only within
this campaign, enforces a size limit, and rejects traversal and external
symlinks. Invalid/incomplete checkpoints are reported and retried.

2026-10-14: added proof flow, exact tree witnesses, dependency graph,
prior-art details and persistent research checkpoints. Thirteen local
dashboard contract tests passed. Scientific acceptance remains a separate
campaign obligation.

## Records and architecture

- `dashboard/dist/`: buildless browser application; no external assets or CDN.
- `dashboard/server.py`: local static/JSON/event-stream server and process observer.
- `dashboard/track.py`: transparent launch wrapper and output recorder.
- `dashboard/telemetry.py`: explicit event helpers for scientific scripts.
- `dashboard/catalog.py`: beginner summaries with source row/line locators.
- `.dashboard/runs/<id>/manifest.json`: job identity, timestamps, and exit status.
- `.dashboard/runs/<id>/events.jsonl`: append-only output, resource, stage,
  metric, check, and artifact events. The UI shows recent output; full events
  remain in the local record. `.dashboard/` is ignored by Git.

The code first consulted `bootloops/tools/README.md` and the full Turnstile
guide. Turnstile manages Linux shared-machine admission and has no macOS
visual observer, while the scientific tools produce computations rather than
a workspace dashboard; this companion wraps the existing launchers without
changing upstream scientific code or verification pins.

## Validation

```sh
.venv/bin/python -m unittest discover -s dashboard -p 'test_*.py' -v
```

The contract tests cover byte-preserved output, success/failure exit codes,
live samples, history after restart, incomplete event writes, PID reuse,
long output preserving earlier semantic checks, scope filtering, and the
read-only API. Fixtures use a separate disposable store under `.dashboard/qa`.
Real integration checks ran the supplied ERAS and Abacus batteries unchanged.

2026-10-14: added the companion observer, browser dashboard, telemetry helpers,
and workspace launcher integration. Previous commands keep their arguments
and exit status and now also leave a local run record. The installation
validation and original scientific source remain unchanged.
