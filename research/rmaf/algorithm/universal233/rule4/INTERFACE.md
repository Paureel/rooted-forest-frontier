# Original Rule4 interface

Author kernel proof; fresh nonauthor acceptance is pending. The full algorithm,
global recurrence, smaller base and novelty remain OPEN.

`select T S` is an executable finite selector. It checks proper equal original
labels, absence of common cherries, absence of Whidden t=1 in both roles, and
the actual Rule4 local geometry. `Choice` contains only those source guards.
`rawChoices_complete` and `select_complete` admit both endpoint orientations and
both traversal orders of the c and X2 original pendant heads. No desired cover,
exchange, minimum, mass or runtime property is an input field.

| Consumer | Proved output |
|---|---|
| `actual_original_exchange` | From the actual original agreement and disputed a-block case: a same-size original agreement refining the two literal source cuts; target topology and global source/target separation are constructed. |
| `actual_rule4_cover` | Every original agreement has a no-larger original agreement refining one of the three source branches. |
| `selected_branches_cover` | The same cover bound directly to the executable selected `branches` list. |
| `all_pendant_literal_regions` | Exact residual original walks, region coverage/separation, original leaf sets, every suppressed vertex, no leafless regions and exact cut-list length. |
| `selected_cut_properties` | Actual valid nonroot distinct incomparable original cut heads, retained original leaf, proper equal-label original targets/sources, positive actual cut cost. |
| `selected_source_state` | Actual checked source partition/embeddings; sourceForest materialization; proper ForestState; original-agreement/refinement equivalence; exact additional cost. No target-Q embedding hypothesis. |
| `selected_swapped_cost` | Swapped ALL-pendant original cost is at least two, derived from the actual no-t1 source guard. |
| `actual_callback_decrease` | Every eligible actual callback strictly reduces the ordinary cut budget. |
| `actual_callback_mass` | For rational c≥2, every actually budget-pruned callback in the list has normalized total mass ≤c⁻¹+2c⁻². |
| `solveForest_minimum` / `solveForest_none_iff` | Under the exact child-specific IH, executable minimum selection returns a minimum original agreement, or None exactly when the budget admits none. |
| `solveCuts_recovery_work` | Actual formal final recovery is charged once by finalPolynomial(S,G)·c^q for rational c≥2, with the completed source-operation qualification. |
| `solveCuts_original` | One final original-source recovery, exact |F|−1 cuts, complete original RealizedOutput and minimum original agreement within budget; no local cut union. |

The branches are, in order:

1. Original target T; cut original source S at cHead and X2Head, cost two.
2. Original target T; cut original source S at its actual a-leaf edge, cost one.
3. Swap target/source to S,T; cut ALL original outgoing a–c path arcs in T,
   cost m≥2. Materialize the source forest from restrictions of original T.

`ExactChild child b r` is printed in Rule4Solve.lean. It requires the supplied
callback to solve the literal `ForestState.agrees (some b.target)
b.sourceForest` query with exact additional-cost budget r, and to return a
minimum labelled partition. These are the explicit recursive IH assumptions.
The parent calls only when b.cost≤q, with r=q−b.cost; q=k−1 at an original
component bound k. No rho convention is implicit.

`solveCuts` runs `solveForest`, then the completed original-source recovery
program once on S. It returns that literal original certificate. The independent
review must assess the qualified polynomial source work in COST-MODEL.md in
addition to the exact kernel statements. Python rule4.py mirrors the same
geometry and checks every returned child on the original trees, but its finite
controls do not independently certify its universal equivalence to Lean.

All theorem names above are in `Universal233.Rule4`. The isolated receipt prints
their exact types in Interfaces.log and audits each actual stored declaration
occurrence before name coalescing, including private/generated declarations.
