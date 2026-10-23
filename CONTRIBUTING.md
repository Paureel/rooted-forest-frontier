# Contributing

Read README.md, AGENTS.md, docs/current-status.md and autoresearch.md first.
Coordinate a concrete task in an existing issue or discussion before beginning
overlapping research. Small improvements, negative results, independent
reproductions, source audits and attribution corrections are welcome.

Use a branch such as `codex/describe-the-task` or another descriptive branch
and submit a focused pull request. The maintainer reviews integration and
acceptance; a passing CI job alone does not select a scientific result.

## Research submission

State the exact claim, input conventions, parameter and domain. Identify the
predecessor, source commit or hash, applicable target/pin, and the first
consuming algorithm call. Include code or pseudocode, known-answer controls,
a deliberate failure with a clean twin, raw small evidence, commands, measured
timings, dependencies, and remaining hypotheses. For a refutation, retain the
smallest measured counterexample and name the class it refutes.

Distinguish proposed statements, executed finite comparisons, checked Lean
declarations, reviewed arguments and accepted full results. If a claim concerns
the exponent, include the complete paid recurrence and all local work. Retain
oracle-contact history and obtain a genuinely separate verification route
before proposing scientific acceptance. Do not use discovery examples as
fresh certification cases after they have influenced the design.

## Checks and files

Run `make check` and the scoped checks affected by the change. Report skipped
checks and missing inputs by name. Run artifact-writing historical replays in
an isolated worktree; keep immutable inputs and prior receipts unchanged.
Files over 1 MiB and generated binaries stay local. Follow docs/large-files.md
for omission records and local restoration. Do not upload private credentials,
unrelated personal files, toolkit caches or entire runtime installations.

## Credit and license

Attribute predecessors and third-party sources, preserve original notices,
and disclose substantial AI assistance. New original contributions are under
Apache-2.0. Do not relicense third-party reference materials. Maintainer:
Aurel Prosz (@Paureel); corrections to credit are welcome through the
attribution issue template. See NOTICE and CONTRIBUTORS.md.
