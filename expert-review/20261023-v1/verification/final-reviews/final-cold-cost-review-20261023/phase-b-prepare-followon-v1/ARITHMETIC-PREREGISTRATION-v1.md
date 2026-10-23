# Additive exact arithmetic calibration

This is a new one-shot calibration of the actual released fee rows and finite optimizer work recurrence. It does not rerun Phase A's different toy fee model or execute the candidate/counter. Expectations below are hand-constructed before this new script executes. They were designed after reading the screened computation, so they are not additional pre-candidate controls or an independent engine claim. No author argument was read.

Existing tool consultation remains the toolkit index and full Emitall guide read in Phase A; Emitall compares receipt claims and does not derive these primitive fees/recurrences. A small one-shot script is justified, with no framework/upstream change. Timing is unknown before execution; fixed work is three word emissions, two tiny scan folds and two deliberate errors. Use existing run_capped.py with BootLoops Python, shared lock, default 30 seconds and fresh directories. No unchanged passed rerun or cap raise.

## Clean expectations

C1: use the exact representation fee rows with w(0)=1. A word emission at next address m with value v executes WRITE(m,v), CONST1 and ADD(m,1,m+1). WRITE costs `1+2*w(m)+2*w(v)+w(m+1)` because u=m equals the pre-heap bound but both operand roles pay. CONST1 costs 2; ADD costs `2+w(m)+w(m+1)`. Exact emission fees for (m,v)=(0,0),(3,1),(8,8) are [12,19,33]. The expanded expression `5+3*w(m)+2*w(v)+2*w(m+1)` must equal those fees independently at all three points. Sum over no emissions is exactly 0. This checks a local fee identity, excluding separate value/tag preparation, frames and all surrounding code.

C2: synthetic sourceOptimizeMeter recurrence inputs: preflight work 7; query outcomes [None,None,Some F] with query debits [3,5,7]; scan adds 12 at every visited trial; recovery work 11; successful finish adds 12; outer successful path adds 8. Therefore scan work=51, finish work=23, complete work=89, trials=3, recoveries=1. These are synthetic work scalars through the printed recurrence, not measured candidate operations or literal completeSourceCounter values.

## Corrupted twins

N1 deletes one of WRITE's two written-value width occurrences for (8,8), yielding emission fee 29 instead of 33. Required diagnostic `WRITE_VALUE_MULTIPLICITY`, expected=33, observed=29.

N2 replaces the two failed query debits by zero while retaining all trial administration and outcomes. It yields complete work 81 instead of 89. Required diagnostic `FAILED_TRIAL_DEBITS_OMITTED`, expected=89, observed=81.

Positive child must record exactly 2 MATCH cases and exit 0. Corrupted child must record exactly 2 CAUGHT cases, with those exact diagnostic values, and exit 23 only after both. Unexpected mismatch/survival exits 1 and remains a calibration failure. Inspect semantic JSON and logs independently of wrapper PASS/exit; retain every failure and correct only prospectively.

No global A, allocation/width envelope or consuming theorem is validated by these small controls. Shared CPython integers and existing wrapper/supervisor are explicitly common infrastructure, with sampled own-tree RSS plus wait4 rather than a continuous kernel/whole-host hard guarantee.
