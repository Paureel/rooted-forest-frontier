# Paid literal decision source model

The paid `LiteralProps` fee has an implemented source inspection bound. `literal_value` proves that `literalMeter` returns the exact frozen decision value. `literal_call_work` bounds each actual bounded request by `literalBudget N`, where `N = |leaves T| + |leaves S|`; the proof applies whether the guard succeeds or fails. `paid_selected_work_concrete` substitutes this implemented fee into the existing paid builder theorem. The classifier's distinct fee contract remains unchanged.

`literal_budget_expanded` proves the exact polynomial

`literalBudget N = 1024*N^5 + 3072*N^4 + 960*N^3 + 640*N^2 + 238*N + 164`.

The units are source primitive inspections. A Nat or Bool comparison counts as one scalar inspection. Recursive tree/list/address scans, construction of the literal bottom tree, bounded quantifiers, repeated leaf extraction, both incident occurrences, and four minimal-vertex occurrences are included. The polynomial is not a bound on native instructions, wall-clock time, binary integer operations, or instrumentation overhead. Those correspondences require their own integration.

The canonical import is `LiteralInterface`; `PUBLIC-INTERFACE-v1.json` gives the exact compatible import paths. `sourceDecision` is an ordinary compiled definition around the frozen `Decidable` instance. Both the frozen decision and the new meter return true on a five-leaf planted geometry whose `LiteralCallDomain` membership is proved in Lean. No noncomputable decision or replacement oracle was used. Theorem axiom closures include the permitted standard axioms `Classical.choice`, `Quot.sound`, and `propext`; the runtime compilation check is separate from that proof inventory.

The canonical replay compiled eight new source modules without rebuilding dependencies. Its stored-producer audit retained all non-theorem bodies and traversed theorem references and axiom closures. The audit inspected 264 new stored declaration occurrences and 243 reached frozen occurrences. The unchanged auditor template rejected direct/private/unused custom axioms and an opaque dependency on a custom axiom. Parser copies with a missing row, duplicate row, foreign object path, custom axiom, or custom dependency axiom were rejected. Two fresh false Lean claims were rejected. All 22 named runtime controls passed; the planted successful decision used 4,374 model inspections, below the `N=10` cap 134,146,544.

This is an author check in the same Lean/tool lineage. No fresh nonauthor verification, native or binary cost result, whole Rule5 result, full 2.33 acceptance, or novelty result is claimed. The isolated target forbids child or sibling coordination. The first remaining source statement is in `FIRST-GAP-v1.md`.

The development records preserve the failed namespace probes, type/elaboration and normalization attempts, a module-name collision refusal before compilation, and one pilot stopped by the live 3 GiB disk floor. The final replay matched all 22,072 prior immutable occurrences by hash, mode, and inode before and after its run. Original writable sources retain their identity and modes. The general toolkit `bootloops-check` suite was not run; the relevant capped Lean source/audit controls were run instead.
