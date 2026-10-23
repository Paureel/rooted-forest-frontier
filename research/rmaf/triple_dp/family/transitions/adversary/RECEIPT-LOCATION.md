# Receipt location correction

The completed adversary interpreted the abbreviated `results/` ownership path
as the workspace-root results directory. Its seven receipt/log files were
moved without changing their bytes into `research/rmaf/results/` after the
run completed. `research/rmaf/results/triple-family-transitions-adversary-relocation.json`
records every original path, canonical path and SHA-256.

The original report, workfile and executed-command fields remain unchanged as
historical evidence. To replay from the workspace root, give `--output` and
`--gate` paths beginning `research/rmaf/results/`, rather than `results/`.
For example, the canonical bounded receipt is
`research/rmaf/results/triple-family-transitions-adversary-bounded.json`.
No checker code, frozen control, numerical result or proof source changed.
