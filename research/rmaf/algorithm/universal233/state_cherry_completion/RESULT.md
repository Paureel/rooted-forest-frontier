# Common-cherry reduction: author proof

The common-cherry reduction is complete as an author Lean proof over the
literal frozen `ForestState` definitions. The grade `CLOSED_UNVERIFIED` means
that the isolated source replay and controls passed; a fresh nonauthor review
has not yet accepted the mathematical statement and its use in the solver.
All three main solver milestones remain OPEN. Source priority, the complete
algorithm, and its runtime remain OPEN.

The canonical author receipt is
`results/algorithm-universal233-state-cherry-20261015T101755Z/certificate.json`.
The replay rebuilt 23 local source modules and recorded origins and allowed
axioms for all 702 declarations in those modules. The observed axiom union was
`Classical.choice`, `Quot.sound`, and `propext`. Every local module resolved to
the isolated output directory; all other modules resolved to the local Lean
installation. The original state-reduction freeze still matched all 77 pinned
files.

## Statements

`ForestState.endpoint_reassignment_embeddings` in Endpoint.lean closes the exact original
minimal-embedding consumer printed in the frozen state-reduction
`OPEN-CONSUMER-v1.md`. The theorem uses actual sibling leaves, proper labels,
the original `minimalVertices`, and a comparison block excluding both
endpoints. Its proof follows the actual cherry address, including root,
singleton-selection, and sibling-swapped cases.

`ForestState.common_cherry_no_larger` in Replacement.lean constructs a literal original-state
agreement with the two endpoints in one block. Its block count is no larger
than the supplied agreement's count. If the endpoints were separated, one
block is a singleton by the frozen separation theorem. The construction
removes that singleton, adds its endpoint to the sibling block, and preserves
each target and source agreement check. The actual source component is
identified by proper label ownership. Other source components remain present.

`ForestState.common_cherry_contract_agreement` in StateContract.lean contracts every coalesced
agreement through the literal `contract` and `contractBlock`. The proof covers
partition validity, a fresh label, restriction topology, original embedding
clearance, and all actual source families. `ForestState.common_cherry_expand_agreement` in StateExpand.lean
expands every reduced agreement through the literal `expandBlock` into an
agreement for the original target and source forest. Expansion is checked
against the original trees; swapped cherry orientation is handled by
`RootedIso`. The block count and the source-component count are unchanged
under their respective list maps.

The complete state decision statement is:

```lean
theorem common_cherry_state_decision_equivalence
    (T : Option Tree) (ss : List Tree) (a b z q : Nat)
    (ready : cherryReady T ss a b z = true) :
    feasible T ss q ↔
      feasible (T.map (contract a b z)) (ss.map (contract a b z)) q
```

`ForestState.common_cherry_state_strict_decrease` in StateExpand.lean proves

```lean
(labels (T.map (contract a b z))).length + 1 = (labels T).length
```

under the same readiness condition. The budget is arbitrary. Additional cost
is the original executable `F.length - ss.length`; the proofs use the actual
number of source components. No replacement agreement, desired transport,
cost equality, or decision equivalence is assumed as a structure field.

## Executed checks

Before writing the new proof, the 19 pinned positive graph/state examples
compiled and four deliberately false claims were rejected. The cases include
the root cherry, singleton selection, an extra selected label, comparison
blocks excluding both endpoints, sibling swaps, different target/source
addresses, another source component, freshness/properness refusals, and the
wrong one-component budget. Permitting `C=[b]` falsifies the weakened endpoint
assertion, as the pinned false control demonstrates.

The final isolated replay recompiled those controls and eight named theorem
consumers. It accepted a known true arithmetic claim and rejected a known
false one. The audit caught an inserted custom axiom, a missing axiom record,
a wrong local module path, a wrong module origin, and changed source bytes.
The `bootloops-check emitall` suite passed. Other toolkit package batteries
were not run because this change adds problem-local Lean proofs and the
problem-local replay checks every formal dependency.

These controls use the original executable definitions and the same author
context as the new proof. They provide development and source-replay evidence.
Fresh nonauthor mathematical acceptance and the fresh-context referee check
remain pending. No independent implementation is claimed.
