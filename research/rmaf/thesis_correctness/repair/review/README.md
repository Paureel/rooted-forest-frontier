# Fresh review records

`REPORT.md` gives the result and limits; `verdict.json` provides the machine-readable classification. `LOCAL-RECONSTRUCTION.md` gives the independently reconstructed component argument and a corridor-specific second-exchange representation supplement. The supplement awaits a further independent read.

The Python programs are one-shot review instruments. They test exact rooted labelled agreement-forest partitions, original-edge cuts, finite normalization cases, and the explicitly listed Lean statements. They use the unary labelled rho model and whole/rho-detached finite search families. A passing finite search means no counterexample occurred in that stated family. It does not prove a universal AF theorem or a global algorithm result.

Run from `/Users/paurel/Documents/ChatGPT/bootscience`:

```
./bootloops-python research/rmaf/thesis_correctness/repair/review/fresh_exact.py
./bootloops-python research/rmaf/thesis_correctness/repair/review/hunt.py
./bootloops-python research/rmaf/thesis_correctness/repair/review/additional_checks.py
./bootloops-python research/rmaf/thesis_correctness/repair/review/consumer_census.py
./bootloops-python research/rmaf/thesis_correctness/repair/review/audit_lean.py
./bootloops-python research/rmaf/thesis_correctness/repair/review/package_review.py
```

Known-answer fixtures and deliberately corrupted outputs precede construction reads in the original run. Replays preserve the scripts and receipt structure; they cannot recreate an agent's original reading order. The programs assert exact Boolean, integer and partition equality and stop on mismatch. The Lean audit requires eight successful builds, two rejected false proofs, unchanged source hashes and the declared axiom allowlist. New outputs remain within this review directory or `results/thesis-correctness-repair-review-*`.
