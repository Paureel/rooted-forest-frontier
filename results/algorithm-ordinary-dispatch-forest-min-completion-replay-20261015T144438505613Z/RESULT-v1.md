# Ordinary callback minimum completion

`ForestMinimumCompletion` proves a mathematical extension of a callback that
is correct at budgets b≤K. The extension is NONCOMPUTABLE proof support. It
does not supply an executable ordinary solver or a runtime bound. Fresh
independent review remains pending; all main algorithm milestones remain open.

`LocalOrdinaryIH` retains the completed GenericForest v3 `OrdinaryIH`
soundness, budget, minimum and completeness semantics, with b≤K added to
each query. Properness guards remain exactly as in the completed interface.
`ghost_eq_actual` proves equality on every t,s,b≤K without any properness or
local-correctness premise. In particular, malformed pairs preserve whatever
the actual callback returns.

`nat_minimum_from_witness` proves Nat well-order by strong induction.
`minimum_from_original_AF` applies it to attainable original-AF component
counts. Its only mathematical input is one actual original agreement forest.
The resulting forest minimizes component count over every original agreement
forest for the pair. A feasible witness also supplies the minimum's budget
bound. No solver, global IH or desired-minimum record premise is used.

The noncomputable `minimumCallback` chooses the derived minimum when an
original feasible AF exists and returns none otherwise. Its soundness,
completeness and exact none criterion are proved. The noncomputable `ghost`
first returns the actual callback for b≤K; beyond K it uses this mathematical
choice. `ghost_global_ordinaryIH` proves the completed global OrdinaryIH from
only LocalOrdinaryIH. `ordinaryIH_extension` packages that extension with
exact equality for all low-budget calls.

The controls derive minimum length one from an actual two-component AF for
identical two-leaf cherries, preserve improper garbage at K=0, preserve all
pair values at b=K, and prove that a high-budget ghost can differ from the
actual callback. Four false claims are rejected. Initial control and proof
failures, including a dependency parser's refusal of bundled Lean, are
preserved with their failing sources or exact diagnostic records.

STACK-PINS binds 76 completed GenericForest v3 dependency modules and three
new modules. The isolated final replay rebuilds their actual original and
adapted source bytes and audits every stored scientific producer occurrence.
Fresh Std-only clean twins, coalesced custom axiom plus own clean declaration
in both orders, private/unused axioms, false proofs, missing/duplicate rows,
foreign paths and source/adapted-byte corruptions test the detector. The
completed detector and sources are author development contacts.

The parent owns bounded callback congruence for the actual solve/disjoint/
schedule implementations. That separate proof is required to transfer a
completed theorem about ghost calls back to actual execution. This package
does not inspect or duplicate it. No executable closure, source-work claim,
improved base, novelty or independent acceptance is claimed. All three main
Algorithm/Correctness/Base milestones remain OPEN.
