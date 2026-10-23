# Preproof common-cherry graph controls

Freeze before proof: exact Lean positive controls in GraphControls.lean and four
deliberately false Lean claims in GraphFalseControls.lean. Every positive must
compile; every negative must fail at `decide` with `is false`.

The graph cases include root cherry with singleton A, nontrivial A with an
additional selected label, C excluding both endpoints, and sibling-swapped
cherries at different original addresses. The C=[b] case is an explicit false
variant: old minimal embedding is clear, reassigned embedding is not clear.
Finite state cases include a second source component, exact additional cost,
improper duplicate taxa, and fresh-label collision refusal.

These are author development controls through original executable definitions;
they are not an independent implementation or a universal proof. The wrong
budget 3-1 deliberately ignores the actual two source components and must fail.
