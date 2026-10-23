# Post-contact control erratum: S11 q4 entry is not a callback

Frozen READY callback table q4 budgets[1] does not match actual callback execution. Exact first comparison FROZEN-CONTROL-FAILURE-S11-q4-v1.json records planned entry budget[1] but reported/observed callbacks[]. Preserve the original READY table and its failed comparison unchanged.

Cause: the hand reference table subtracted q-d and promoted the remaining ordinary ENTRY to a recursive callback. For S11 its sole unresolved B block has minimum3. Actual pretest01 rejects it (hard slot), and the paid scheduler's knownCost+2*pending guard refuses an ordinary remaining budget1 before recursion. Thus q4 has no recursive call. The frozen abstract arithmetic trace [3]/budget1 remains a valid arithmetic fixture; it was never asserted in root TARGET to be this literal fixture's runtime trace. This arm's S11-specific promotion was invalid.

Correction scope: interpret original q4 [1] as a planned entry budget only, with a separately named post-contact reference observation of empty actual call trace. This correction is not an original blind passing control and not evidence of a candidate defect. All original expected lists, graph bank, source-core outputs, q5[2,0,0] and q6[3,1,1] predictions remain frozen and must still be compared without tuning. No candidate source edit is made.
