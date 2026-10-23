# BootLoops local installation

The [local monitoring dashboard](http://127.0.0.1:8765) shows live workspace
runs, history, the toolkit map, and an interactive idle demonstration.
Start it with `./bootloops-dashboard`. See
[`dashboard/README.md`](dashboard/README.md) for recording and explicit telemetry.

The [official BootLoops toolkit](https://github.com/BootLoops-ai/bootloops)
is installed in `bootloops/`. Its
[companion skills](https://github.com/BootLoops-ai/skills) are checked out in
`bootloops-skills/`, and all 12 skills are installed for this Codex project
in `.agents/skills/`. The skills are available to Codex from the next turn.

## Using it

In this Codex chat, describe your scientific problem and ask to use BootLoops.
The project instructions point agents to the toolkit index and relevant guides.

For terminal use:

```sh
cd /Users/paurel/Documents/ChatGPT/bootscience
source ./activate.sh
python3
```

Alternatively, run scripts without activating your shell:

```sh
./bootloops-python your_script.py
./bootloops-check
./bootloops-check mixalot eras
./bootloops-dashboard
```

The Python launcher adds the toolkit to `PYTHONPATH`; activation also makes
the local Julia and PARI/GP runtimes available. The toolkit index is
[`bootloops/tools/README.md`](bootloops/tools/README.md), and each tool has a
guide describing its inputs, entry points, and acceptance checks. There is
no single BootLoops application to open: this is a toolkit operated by an
agent or Python scripts.

## Installed components

- Toolkit and companion skill sources, pinned to the commits in
  [`installation.json`](installation.json).
- A dedicated Python 3.12 environment in `.venv/`, with the common core,
  per-package Python dependencies, PARI bindings, and population-genetics
  simulation dependencies. Exact versions are in
  [`requirements.lock.txt`](requirements.lock.txt).
- Official Julia 1.11.9 for Apple Silicon, with a project-local package
  depot and the committed package environments supplied by BootLoops.
- PARI/GP 2.19.0 built locally with thread-local stacks and its native
  arithmetic kernel. Native source and binary downloads were checked against
  the published SHA-256 checksums.
- The seven protocol skills and five research skills, installed only in
  this workspace and checked byte-for-byte against their pinned source.

The Python environment uses the bundled Codex Python runtime listed in
`installation.json`. If that base runtime is removed by an app/runtime
update, recreate `.venv/` with Python 3.12 and install
`requirements.lock.txt`.

External engines such as Kira, Blade, AMFlow.cpp, FORM, and Singular are
installed when a calculation needs them, following BootLoops' installation
instructions. Tool batteries name skipped engine-dependent checks. A passing
battery can contain these explicit skips; it does not certify an engine that
was not installed.

## Validation records

The combined verification result is **45 package batteries passed, three
refused because reference data is absent, and two failed in Linux-specific
process-management checks on macOS**. All seven package checks rerun after
preparing Julia passed, including Abacus and Counterweight.

The expected data refusals are `ffcapital`, `frobenius-boundary`, and
`galois`. The two remaining failures are `amflow-kit` and `seedling`: their
process/memory-fence and cgroup checks require Linux's `/proc` filesystem.
These failures remain recorded as failures; they were not bypassed or
converted to passes. Run those process-management components on Linux when
needed.

The supplied verification scripts and integrity pins are unchanged.
`installation-initial-selftests.json` preserves the first run of all 50
package batteries. `installation-native-rechecks.json` records the checks
rerun after installing PARI and allowing the sampler's process inspection.
`installation-julia-rechecks.json` records all seven passing native-tool
rechecks after Julia setup.
The final combined record and its limitations are in
`installation-validation.json`.

The complete suite can be rerun with `./bootloops-check`. It writes
`bootloops/selftest_results.json` and returns a nonzero exit status if any
package battery fails; expected data refusals do not cause a failing exit.

To remove this installation, remove this workspace's downloaded checkouts,
`.venv/`, `.runtime/`, and `.agents/skills/`. No global shell configuration
or system package manager is changed.
