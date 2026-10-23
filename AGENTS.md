# Repository instructions

Maintainer: Aurel Prosz (@Paureel). Original contributions: Apache-2.0.
Start with README.md, docs/current-status.md, autoresearch.md, the applicable
research README, and the target/pin governing the exact task. Treat older
claims of "current" status as historical records. This repository remains
private unless the maintainer explicitly requests a visibility change.

## Research requirements

- Read research/rmaf/spec.json and research/rmaf/algorithm/{TARGET,PIN}.md.
  Ordinary rooted binary rMAF, k components, q=k-1 cuts; no implicit rho.
- Consult the installed protocols in .agents/skills/. For scientific work,
  consult bootloops/tools/README.md and the relevant guide when the optional
  toolkit is installed. Use ./bootloops-python for Python and ./bootloops-lean
  or ./bootloops-lake for Lean. Run the supplied ./bootloops-check when changing
  toolkit code; record unavailable engines and skipped checks explicitly.
- Preserve original verification scripts, frozen sources, hash pins, failed
  candidates, counterexamples, alpha registrations and prior reviews. Append
  versioned corrections. Never repair a frozen record by overwriting it.
- Freeze positive/negative controls before the real run; execute a deliberately
  false comparison. Finite tests do not prove general correctness or a smaller
  exponent. Track solver/oracle contact and the deepest shared dependency.
- Account for all branches, eligibility tests, preprocessing, local optimizers,
  source generation, reconstruction, bit costs and parameter conversions.
  Every imported lemma must match the actual consuming call's hypotheses.
- Lean claims require their exact sources, toolchain, successful replay,
  explicit theorem inventory, and axiom audit. Compilation of a conditional
  statement does not establish its hypotheses. Preserve negative proof controls.
- Claim novelty only after the full-text literature protocol, including the
  retained prior-work questions. The source-reported baseline is not an
  independently certified current literature record.
- Use an isolated worktree for research that writes evidence. Measure a pilot
  before expanding compute. Record actual scientific output units, not CPU use.

## Repository work

Run make check after changing packaging, collaboration files or wrappers.
Keep individual Git files at or below 1 MiB. Read docs/large-files.md before
restoring an omitted input. Do not add binaries, runtimes, caches or secrets.
Do not claim the import manifest covers later research commits; append a new
versioned manifest for any added import. Do not change visibility or publish
outside the requested GitHub repository without maintainer authorization.

## Standing user preferences

Sites may be used for local design, build, test, packaging and preview only.
Never deploy, publish or upload source, data, snapshots or plots to Sites.
Keep Sites apps and previews local.

For any new or continued Discovery Radar campaign, prediction improvement and
its uncertainty are descriptive only and excluded from primary support,
biological confirmation and novelty acceptance. Preserve biological confidence
intervals, multiplicity/statistical thresholds, effect-size/robustness,
matched-assay/source checks, independent numerical verification, fresh
biological confirmation and novelty review. Record versioned amendments;
preserve frozen protocols, results and alpha registrations; label retrospective
rescoring as post hoc sensitivity. In O-NET resolve effective rules from
docs/radar-acceptance-policy.json and campaign-test-policy-current.json.

The original workspace instructions and setup are preserved under
docs/import/original-setup/. Historical absolute paths name the source
workspace; they are not portable clone paths.
