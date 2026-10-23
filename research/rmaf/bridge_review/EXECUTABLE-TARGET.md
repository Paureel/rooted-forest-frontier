# Executable hull interface target — 2026-10-14

Continue the completed graph-support review toward the existing executable
model. This target does not license a faster-bound claim.

For `RMAF.Tree t` and selected natural-number labels S, prove that
`RMAF.minimalVertices S t`, when nonempty, is graph-connected using exactly
`BridgeReview.Adj` and `Walk`. Construct `ConnectedSupport` with precisely
the same vertex membership, and compose with `toRootedRegion` and the
original deepest-root consumer. Derive nonemptiness from an actual selected
leaf occurring in t. Do not assume connectedness, convexity, ancestry, or
correctness of the extraction function being certified.

May assume: Lean Std; the frozen executable definitions in `../lean/RMAF.lean`;
the audited graph-support theorems and their explicit hypotheses. Preserve
these sources and existing receipts. New proof files must import freshly
rebuilt dependencies. Standard axioms only; no placeholders or native_decide.

Exact hand controls before proof construction, with false=left, true=right:
for t=((0,1),(2,3)), S={0,2} has support
{[],[false],[false,false],[true],[true,false]}; S={1} has support
{[false,true]}; S={0,1} has support
{[false],[false,false],[false,true]}; S={} and S={9} have empty support.
Deliberately deleting a path vertex from the first case must be rejected.
Record any source/spec disagreement before changing either expectation.

An acceptable partial result proves the exact executable connectivity and
consumer composition while retaining leastness, unique-label interpretation,
and source/target restriction transport as named open obligations. Do not
rename the full graph-semantic interface closed unless those stronger
properties are actually proved. Prefer structural induction over larger
enumerations. A fresh adversarial/semantic check must inspect the final
interface and malformed negative-control diagnostics.

Own new files under `bridge_review/executable/`, receipts under
`../results/bridge-executable-*`, and progress `../progress/bridge-executable.json`.
Other agents own region-family DP and thesis correctness/runtime. Do not
change their code or restart their work.
