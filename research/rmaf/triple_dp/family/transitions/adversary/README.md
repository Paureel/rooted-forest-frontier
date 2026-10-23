# Independent merge adversary

This problem-specific instrument tests the finite geometric merge specified
in `../TARGET.md`. It checks convex supports with undirected graph paths and
compares them with a separately implemented prefix/owner method. It is kept
beside this problem deliberately; it is not a general toolkit package.

Use it to replay the frozen merge controls or the declared small search.
It does not check child restriction, DP color legality, automata, Python DP
tables, or arbitrary proof statements. `REPORT.md` describes the result and
source audit; `SPEC.md` records the pre-execution method and stop rules.

`CONTROLS-PASS` means every positive, negative and clean-twin assertion in the
specified battery passed. `NO-FIRE-BOUNDED` means no counterexample occurred
in the printed denominator. `CONTROL-FAILURE`, `CHECKER-DISAGREEMENT`, or
`FIRE` ends the run with a nonzero exit and a retained diagnostic. A successful
process exit does not establish a universal theorem.

Before using a bounded observation, require the complete frozen control
battery, the copied-checker mutation audit, and a measured pilot with matching
source hashes. These executions and their receipts are retained. A separate
author must still review universal proof claims. The two local routes share
one author and the pinned problem semantics.
