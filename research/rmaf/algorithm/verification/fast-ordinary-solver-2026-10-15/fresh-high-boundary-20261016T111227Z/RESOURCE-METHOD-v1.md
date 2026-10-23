# Resource method before proof

No proof is run before guard qualification. The required skills and original toolkit index were read in the preceding stage and remain applicable. For this stage I read `bootloops/ops/README.md` and the Turnstile guide. Turnstile explicitly does not cap memory and refuses Darwin. Filename-only searches of permitted tool locations found no installed bounded Lean launcher. A narrow filename search incidentally listed unrelated source filenames; none was opened.

Tool-stewardship decision: use the installed `bootloops-python`/`bootloops-lean` launchers unchanged, and test whether the installed process library can supervise its own children on this host. If live child memory measurement cannot be established, stop before proof. A target-local supervisor is justified because Turnstile is neither a Darwin runner nor a memory limiter.

The guard qualification uses scaled thresholds and tiny producers. It must pass a clean producer and detect wall, raw, line, compressed, memory and spawned-child memory excesses before the first proof. Missing memory samples, untracked children, output/export bounds or guard crashes must reject the run. The real limits remain RSS 3072 MiB, raw 16 MiB, line 8 MiB, compressed total 256 MiB, and a live 3 GiB disk floor. Initial pilots are at most 30 seconds; audits at most 59 seconds. Proof exports must be emitted as bounded DAG records/chunks, with no expression-tree `reprStr` dump.

Historical failures in the original frozen stage remain failures. Passing this stage's guard will authorize only new runs.
