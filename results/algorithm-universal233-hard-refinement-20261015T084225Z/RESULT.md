# Original hard-parent refinement

The author proof establishes the original hard2 branching cover in Lean. It does not establish the complete faster rooted-MAF algorithm. All three main algorithm milestones remain OPEN. Fresh hostile and nonauthor acceptance review is pending.

`Safety.actual_hard2_source_safety` accepts the original `RMAF.agreement T S F = true`, the source's distinct original labels, an actual unsuppressed target cherry, and exactly two original pendant child edges. It constructs the two source edges, their three literal original residual components, the ordinary partition check, and the alternative `[a] ∈ F` or `[b] ∈ F` or `F` refines those three components. `actual_hard2_unordered_safety` admits either sibling orientation.

`Components.original_pendant_spec` proves that the executable edge list is exactly the original directed child edges whose tails lie on the unique a–b path and whose heads do not. `LiteralOriginalThree` characterizes actual residual walks after deleting those two original edges. It proves coverage and separation of all original vertices, literal leaf-set equivalence, nonempty leaf sets for all three components, and absence of leafless components. `Safety.hard2_endpoints_in_root` places a,b in the third component.

The proof does not assume a supplied refinement, reachability record, ownership selector, cut history, or a local cut-subset condition. The actual agreement checker supplies the needed embedding disjointness. The common-block step transports the target cherry through `restrict` and `RootedIso`; siblings above the source LCA remain unrestricted.

Run `./bootloops-python research/rmaf/algorithm/universal233/hard_parent_refinement/replay.py` from the workspace root. Each run copies exact sources into a new local `results/algorithm-universal233-hard-refinement-*` receipt, rebuilds all modules, inventories generated and private declarations by module origin, checks their recursive axiom dependencies, executes positive and false controls, catches missing records and a hidden private custom axiom, checks source pins, and makes the completed receipt read-only.

The finite controls are development and interface checks. They do not provide independent verification of the universal theorem. The proof has not been reviewed by its own author as a substitute for a fresh verifier. Priority rules 4–7, global histories, source selection, homeomorphic-parent exchange, polynomial implementation work, global termination/reconstruction, and improved algorithm acceptance remain separate.
