# BootLoops workspace

The official toolkit is installed in `bootloops/`; its companion protocol
repository is in `bootloops-skills/`. All 12 companion skills are installed
for this project in `.agents/skills/`.

For scientific tasks, consult `bootloops/tools/README.md`, then the relevant
tool's guide and applicable skills before choosing a method. Run Python with
`./bootloops-python` or source `./activate.sh`; the macOS system Python lacks
the required dependencies. Run the supplied validation suite with
`./bootloops-check`. Native runtimes and caches are local to `.runtime/`.

The local dashboard is started with `./bootloops-dashboard` and served at
`http://127.0.0.1:8765`. `bootloops-python` and `bootloops-check` automatically
record jobs for its history. For meaningful internal stage/progress reporting,
consult `dashboard/README.md` and use the optional `telemetry` helpers. Report
scientific checks only after executing them and retaining their evidence;
never translate CPU activity or exit status into scientific acceptance.

Preserve upstream verification scripts, integrity pins, and frozen results.
Report skipped checks, unavailable engines, and platform limitations explicitly.

## Global user preferences

### ChatGPT Sites

The Sites skill may be used to design, build, test, package, and preview apps
locally. Never deploy or publish apps to ChatGPT Sites, or upload app source,
data, snapshots, or plots to Sites hosting. Skip Sites hosting registration
and deployment steps; keep apps and previews local. This standing user
preference takes precedence over Sites skill defaults that require hosting
or deployment.

### Discovery Radar acceptance

For every new or continued Radar campaign, exclude prediction improvement
and prediction-improvement uncertainty from primary support, biological
confirmation, and novelty acceptance. Prediction metrics may be reported
descriptively but must not block scientific verification. Keep biological
effect confidence intervals, statistical/multiplicity thresholds, effect-size
and robustness requirements, matched-assay/source checks, independent
numerical verification, fresh biological confirmation, and novelty review
unchanged.

Record versioned policy amendments, preserve original frozen protocols/results
and alpha registrations, and label retrospective rescoring as a post hoc
policy sensitivity. For the O-NET workspace, use
`docs/radar-acceptance-policy.json` and the campaign's
`campaign-test-policy-current.json` to resolve the effective rules before
continuing or freezing new experiments.
