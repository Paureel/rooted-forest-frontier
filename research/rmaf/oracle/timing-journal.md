# Oracle timing journal

2026-10-14, local macOS arm64, workspace `.venv`, `./bootloops-python`.

Initial exact enumeration used the production CLI, frozen controls first:

- n=3: 3 canonical trees, 9 ordered pairs, 5 partitions; compute loop 0.000047083 s.
- n=4: 15 canonical trees, 225 ordered pairs, 15 partitions; compute loop 0.002646916 s.

Before extending: n=5 has 105 trees and 52 partitions. Scaling the measured n=4
compute window by ordered-pair factor 49 and partition-count factor 52/15 gives
0.450 s. This is a projection under an explicit linear per-partition-work
assumption, not a runtime bound; progress JSON writes and startup are additional.
The pilot is small enough that constant overhead is material. Proceed with a
bounded n=5 run and measure directly; do not extrapolate to n=6 or larger.
Real progress is the number of completed exact tree-pair optima, retained in the
corpus JSON. CPU and log volume do not count as progress.

The n=3,4 receipt is retained at `results/oracle-corpus-n3-n4.json` before the
extended report is generated. Fixture hashes remain unchanged.

Measured extension: n=5 compute loop 0.22065975 s for 11,025 ordered pairs.
Before the six-leaf sample, `sample-plan-v1.json` froze 2,000 input pair indices
and projected roughly 0.156 s compute using the measured n=5 window, with fresh
cache/output overhead named separately. The actual sample took 0.163740542 s
setup and 0.1074245 s compute, completing all 2,000 requested pairs. No larger
run was launched; the first t=2 counterexample already settles that candidate.
