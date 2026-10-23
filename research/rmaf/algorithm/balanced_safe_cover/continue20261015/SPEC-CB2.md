# GLOBAL-CB2 — paid residual-CNF dominance and DAG sharing

Versioned continuation of CB1, frozen before CB2 implementation tests,
2026-10-15. CB1 source and receipts remain unchanged. No alpha/theta target is
moved. This is a GLOBAL original-edge conflict construction, with no local
colored-source or joint-macro import.

## Executable change

At every residual conflict state, repeatedly apply C4 maximal-column
projection and row subsumption. If a projected row is a singleton {e}, select
that original edge and remove every row it hits. Repeat until the remaining
minimum row has at least two edges or no rows remain. This structural closure
makes no optimization query. It costs polynomial time and records each edge.

For every edge e of the next minimum row, form the residual child and run the
same structural closure. Its prefix cost delta is 1 plus its forced cuts.
Before recursion, prune children only by this explicit sufficient relation:
child i dominates child j if delta_i<=delta_j and every row of state_i
contains some row of state_j. Thus every transversal of state_j also hits
state_i. Substituting prefix_i plus the old residual witness for prefix_j
never increases the total number of original edges. Preserve one
representative of mutually equivalent children. The implication test is paid
polynomial work; it is not a distance or optimum oracle.

Recursively solve retained children in fixed order, charging their actual
prefix cost. Cache exact residual-row-mask/budget states. Cached witnesses
use ORIGINAL edge indices; no graph isomorphism test or uncharged relabeling
is allowed. Root incidence factors and factor-specific iterative budgets are
as in CB1. At a successful decision budget, union the selected factor minima,
validate the complete original graph certificate, and emit one full ORIGINAL
optimum, all-compatible/tau0. Failure on insufficient budget is explicit.

## Remaining theorem and falsifiers

The exact outstanding algorithmic statement is a bound on the total number
of reachable compiled residual states, with ALL state compilation and failed
budget searches counted. No bound of (5/4)^b or (3/2)^b is asserted. For a
simple uniform recurrence one would need sum alpha^(-delta)<=1 at every
retained nonterminal branch (or a stronger proved global charging theorem).
A source-realized node whose mass exceeds the benchmark kills only that
uniform recurrence, not the solver's correctness or more global amortization.
A generic rank or small finite execution is not a global theorem.

This variant is motivated by CB1's recorded ordinary matched-m3 root, where
four unit branches produce only two distinct literal residual row families,
and by the crossed-quartet child singleton closures. Those observations are
production-side discovery and cannot independently certify CB2.

## Controls frozen before running

Reuse all literal CB1 abstract and ordinary expected optima, failure-budget
twins, larger-budget ORIGINAL-optimum checks, original-edge/cost/component
checks and production oracle bans. Add exact abstract domination controls:

- rows_A=[{0}], rows_B=[{0,1}]: A implies B; B does not imply A.
- rows_A=[], rows_B=[{0}]: B implies A; A does not imply B.
- equal four-of-five rows [15,23,27,29,30]: after every branch structural
  closure is terminal with total prefix2, so retain one equivalent child.
- triangle [3,6,5]: each child structurally finishes at cost2; retain one.
- abstract nontrivial child comparison: (delta1, rows[{0,1}]) dominates
  (delta2, rows[{0}]); reverse fails on both cost and implication.

Corrupt a stored child delta by -1, corrupt a claimed row implication by
reversing the singleton/two-edge example, and duplicate a cut index; the
actual verifier must reject each with a successful clean twin. The control
harness is same-author production evidence. Fresh nonauthor review remains
required. No full old census or broad toolkit suite is rerun.
