# Explicit lower-fact reuse

These are generic restriction/list facts, not a pendant, coverage, exchange, or solver theorem. Exact statements were read in the isolated `LowerTypes03` run. `LowerGrant04` traversed their stored types/bodies and recursor rules: 387 declarations, axioms `propext` and `Quot.sound`, no forbidden/missing/unsafe/partial dependency. Its 26 nonstandard declaration records were losslessly saved and structurally read back in `exports/lower-grant-v1.body.olean` (3,144 bytes), with imported-region context retained in the bounded JSON-lines log. These facts receive REUSED credit only, with zero independent reconstruction credit.

* `RestrictionBridge.restricted_labels_exact (t u) (U) (hr : restrict U t = some u) {x}` states `x ∈ leaves u ↔ x ∈ leaves t ∧ x ∈ U`.
* `RestrictionBridge.restriction_exists (t) (U) (h : ∃ x, x ∈ leaves t ∧ x ∈ U)` states `∃ u, restrict U t = some u`.
* `RestrictionBridge.restrict_labels (t u) (U) (hr : restrict U t = some u)` states `leaves u = (leaves t).filter (fun x => U.contains x)`.
* `RestrictionBridge.root_not_prepend (s) (a)` states `¬ [] ∈ prependSide s a`. Its generated simplification wrapper remains explicitly reused as in the preceding stage.

All other generic fact statements read in `LowerTypes03` are merely retrieved statements; they are not granted or used unless a later explicit audit qualifies them. The original list-fact source contact and historical resource failures remain unchanged.

Native archive contract: the installed `Lean.CompactedRegion` implementation stores the shared object graph. Save/read use the identical erased `Array StageAudit.BodyRecord` type, identical executable, no closures, and the same live dependency regions. Native binary corruption is checked by SHA256 before any later native parse. The serializer's unsafe IO API is an audit instrument; mathematical dependencies are separately rejected if unsafe or partial.
