# Parameter convention

The inherited Lean interfaces call the current remaining-cut budget `k`.
Thus `OriginalWithin T S k` means an original agreement forest F with
`F.length-1≤k`. At the global optimum component count k_opt, the initial
cut budget is q=k_opt-1. No rho leaf or parameter shift is implicit.

The selected consumers preserve `remaining k c` exactly. Their paid costs
are 1 and 2; the theorem argument `k` must be interpreted as the cut budget at
that call, not as an optimum component count. The result remains conditional
on each actual emitted child's bounded IH.
