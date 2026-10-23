# Contributing research effort

Aim for one independently reviewable result: a scoped lemma, a counterexample,
a verified interface, a source audit, or an executable reproduction. Read
AGENTS.md, docs/current-status.md, docs/task-catalog.json, the relevant original
target/pin, and existing issues/discussions before choosing work.

1. Fetch the canonical repository and pin the main commit. Check whether your
   intended scope is already being investigated. A task catalogue entry is a
   starting point; it does not establish that the task is still open.
2. Define the exact object, parameter range and consumer. Name the unmet
   implication and the result that would change the next decision. Avoid
   repeating an archived failed formulation under a new name.
3. Record a short task card using docs/templates/task.md. Choose a bounded
   initial compute budget, freeze known-answer and corruption controls, and
   measure a pilot. Check existing toolkit capability before writing code.
4. Work in an isolated worktree. Append evidence and contacts as they occur.
   Do not read another verifier's withheld material or present contacted cases
   as fresh. Preserve all original pins and source files.
5. Before submission, fetch main again, inspect related work, and state the
   exact checked source revision. Run make check plus the relevant scoped
   mathematical or formal checks. Record unexecuted checks and open hypotheses.
6. Submit the smallest useful result with a reproducible command, retained
   evidence, predecessor credit and explicit limits. A failed candidate can
   be a useful contribution when its domain and witness are precise.

## Task families

Use docs/task-catalog.json and the latest archived progress/monitoring records
to choose the exact pending obligation. Candidate families include ordinary
source generation, scheduler/branch costs, Rule5 consumer interfaces, witness
reconstruction, and fresh semantic/formal review. Several were active during
the import; coordinate before duplicating them.

Do not launch a new theorem campaign merely to fill a task list. A supporting
lemma needs an actual consumer. The broader claim is accepted only after a
complete algorithm, correctness/termination argument, full worst-case cost
proof, fresh independent verification and literature review meet the existing
campaign criteria. No unattended recurring research job is created by this file.
