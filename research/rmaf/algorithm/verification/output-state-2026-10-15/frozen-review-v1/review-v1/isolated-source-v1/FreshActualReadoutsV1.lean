import ActualConsumers
import Lean
open RMAF RestrictionBridge ForestState ForestGroups OutputState
namespace FreshOutputReadouts
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
def treeJson : Tree → Lean.Json
 | .leaf x => Lean.toJson x
 | .node a b => Lean.Json.arr #[treeJson a,treeJson b]
def forestJson (ss : List Tree) : Lean.Json := Lean.Json.arr ((ss.map treeJson).toArray)
def freshRefines (F Q : List (List Nat)) : Bool := F.all fun B => Q.any (contained B)
theorem refines_readout_exact (F Q : List (List Nat)) :
 freshRefines F Q = true ↔ Refines F Q := by
 simp only [freshRefines,Refines,List.all_eq_true,List.any_eq_true,contained_iff]
def printObj (id : String) (fields : List (String × Lean.Json)) : IO Unit :=
 IO.println ("READ|" ++ id ++ "|" ++ (Lean.Json.mkObj fields).compress)
def literal (id : String) (S T : Tree) (Q F : List (List Nat)) : IO Unit := do
 let ss := sourceForest S Q
 printObj id [("sources",forestJson ss),("source_count",Lean.toJson ss.length),
 ("Q_checked",Lean.toJson (partitionCheck (leaves S) Q)),
 ("source_Q_clear",Lean.toJson (pairwiseEmbeddings S Q)),("target_Q_clear",Lean.toJson (pairwiseEmbeddings T Q)),
 ("state",Lean.toJson (agrees (some T) ss F)),("original_AF",Lean.toJson (agreement T S F)),
 ("refines",Lean.toJson (freshRefines F Q)),("additional",Lean.toJson (additionalCost ss F)),
 ("Q_subtraction",Lean.toJson (F.length-Q.length)),("proper",Lean.toJson (proper (some T) ss))]
def guard (id : String) (T : Option Tree) (ss : List Tree) (F : List (List Nat)) : IO Unit :=
 printObj id [("proper",Lean.toJson (proper T ss)),("state",Lean.toJson (agrees T ss F)),("additional",Lean.toJson (additionalCost ss F))]
def priorityBool (T : Tree) (a : Tree) (bs cs : List Tree) : Bool :=
 bs.all (fun b => disjointVertices (minimalVertices (leaves a) T) (minimalVertices (leaves b) T)) &&
 cs.all (fun c => disjointVertices (minimalVertices (leaves a) T) (minimalVertices (leaves c) T)) &&
 bs.all (fun b => cs.all (fun c => disjointVertices (minimalVertices (leaves b) T) (minimalVertices (leaves c) T)))

#eval literal "target_overlap_refined" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,1],[2],[3]]

#eval literal "target_overlap_Q_invalid" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,1],[2,3]]

#eval literal "source_overlap_omitted_guard" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0,1],[2,3]]

#eval literal "full_Q_one_source" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1,2,3]] [[0,1],[2],[3]]

#eval literal "singleton_Q_zero" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0],[1],[2],[3]] [[0],[1],[2],[3]]

#eval literal "singleton_Q_forces_refinement" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0],[1],[2],[3]] [[0,1],[2],[3]]

#eval literal "singleton_original" (.leaf 0) (.leaf 0) [[0]] [[0]]

#eval literal "reordered_lists_literal_sources" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[3,2],[1,0]] [[3],[2],[1,0]]

#eval literal "empty_Q_no_empty_Tree" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [] [[0],[1],[2],[3]]

#eval literal "empty_block_dropped_unchecked" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[],[2,3]] [[0,1],[2],[3]]

#eval literal "absent_block_dropped_unchecked" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[8],[2,3]] [[0,1],[2],[3]]

#eval literal "duplicate_block_rejected" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[0,1],[2,3]] [[0,1],[2],[3]]

#eval literal "repeat_label_Q_restriction_ignores_repeat" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,0,1],[2,3]] [[0,1],[2],[3]]

#eval literal "absent_label_inside_Q" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1,8],[2,3]] [[0,1],[2],[3]]

#eval literal "missing_label_Q_rejected" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2]] [[0,1],[2],[3]]

#eval literal "empty_final_block_rejected" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,1],[],[2],[3]]

#eval literal "repeated_final_label_rejected" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,0,1],[2],[3]]

#eval literal "absent_final_label_rejected" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,1],[2],[3],[8]]

#eval literal "wrong_rooted_topology_rejected" (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [[0,1,2]] [[0,1,2]]

#eval literal "wrong_rooted_split_accepted" (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [[0,1,2]] [[0,1],[2]]

#eval literal "grouped_B_singletons" (.node (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))) (.leaf 7)) (.node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 5) (.leaf 6)))) (.leaf 7)) [[0,1,2],[3,5],[4,6],[7]] [[0,1],[2],[3],[5],[4],[6],[7]]

#eval literal "grouped_B_cheaper" (.node (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))) (.leaf 7)) (.node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 5) (.leaf 6)))) (.leaf 7)) [[0,1,2],[3,5],[4,6],[7]] [[0,1],[2],[3,5],[4],[6],[7]]

#eval literal "grouped_omitted_B_piece" (.node (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))) (.leaf 7)) (.node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 5) (.leaf 6)))) (.leaf 7)) [[0,1,2],[3,5],[4,6],[7]] [[0,1],[2],[3,5],[7]]

#eval literal "grouped_unsplit_A_fabricated_zero" (.node (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))) (.leaf 7)) (.node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 5) (.leaf 6)))) (.leaf 7)) [[0,1,2],[3,5],[4,6],[7]] [[0,1,2],[3,5],[4],[6],[7]]

#eval guard "guard.none_empty_state" none [] []

#eval guard "guard.none_nonempty_source" none [(.leaf 0)] [[0]]

#eval guard "guard.some_target_empty_sources" (some (.leaf 0)) [] [[0]]

#eval guard "guard.repeated_target_labels" (some (.node (.leaf 0) (.leaf 0))) [(.leaf 0)] [[0]]

#eval guard "guard.repeated_source_labels" (some (.leaf 0)) [(.node (.leaf 0) (.leaf 0))] [[0]]

#eval guard "guard.repeated_source_component" (some (.node (.leaf 0) (.leaf 1))) [(.leaf 0),(.leaf 0),(.leaf 1)] [[0],[1]]

#eval guard "guard.whole_source_cross_block_refinement" (some (.node (.leaf 0) (.leaf 1))) [(.leaf 0),(.leaf 1)] [[0,1]]

#eval literal "bank.target_overlap.0" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0],[1],[2],[3]]

#eval literal "bank.target_overlap.1" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,1],[2],[3]]

#eval literal "bank.target_overlap.2" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,2],[1],[3]]

#eval literal "bank.target_overlap.3" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,3],[1],[2]]

#eval literal "bank.target_overlap.4" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0],[1,2],[3]]

#eval literal "bank.target_overlap.5" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,1,2],[3]]

#eval literal "bank.target_overlap.6" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,3],[1,2]]

#eval literal "bank.target_overlap.7" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0],[1,3],[2]]

#eval literal "bank.target_overlap.8" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,1,3],[2]]

#eval literal "bank.target_overlap.9" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,2],[1,3]]

#eval literal "bank.target_overlap.10" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0],[1],[2,3]]

#eval literal "bank.target_overlap.11" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,1],[2,3]]

#eval literal "bank.target_overlap.12" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,2,3],[1]]

#eval literal "bank.target_overlap.13" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0],[1,2,3]]

#eval literal "bank.target_overlap.14" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] [[0,1,2,3]]

#eval literal "bank.source_overlap.0" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0],[1],[2],[3]]

#eval literal "bank.source_overlap.1" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0,1],[2],[3]]

#eval literal "bank.source_overlap.2" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0,2],[1],[3]]

#eval literal "bank.source_overlap.3" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0,3],[1],[2]]

#eval literal "bank.source_overlap.4" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0],[1,2],[3]]

#eval literal "bank.source_overlap.5" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0,1,2],[3]]

#eval literal "bank.source_overlap.6" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0,3],[1,2]]

#eval literal "bank.source_overlap.7" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0],[1,3],[2]]

#eval literal "bank.source_overlap.8" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0,1,3],[2]]

#eval literal "bank.source_overlap.9" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0,2],[1,3]]

#eval literal "bank.source_overlap.10" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0],[1],[2,3]]

#eval literal "bank.source_overlap.11" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0,1],[2,3]]

#eval literal "bank.source_overlap.12" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0,2,3],[1]]

#eval literal "bank.source_overlap.13" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0],[1,2,3]]

#eval literal "bank.source_overlap.14" (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[2,3]] [[0,1,2,3]]

def groupS : Tree := (.node (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))) (.leaf 7))
def groupT : Tree := (.node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 5) (.leaf 6)))) (.leaf 7))
def groupQ : List (List Nat) := [[0,1,2],[3,5],[4,6],[7]]
def groupA : List Nat := [0,1,2]
def groupB : List Nat := [3,5,4,6]
def groupC : List Nat := [7]
def fa : List (List Nat) := [[0,1],[2]]
def fc : List (List Nat) := [[7]]
def fbSingles : List (List Nat) := [[3],[5],[4],[6]]
def fbCheap : List (List Nat) := [[3,5],[4],[6]]
def groupSs := sourceForest groupS groupQ
def groupBs := owned groupSs groupB
def groupAs := owned groupSs groupA
def groupCs := owned groupSs groupC
#eval printObj "group" [
 ("A_cost",Lean.toJson (additionalCost groupAs fa)),("C_cost",Lean.toJson (additionalCost groupCs fc)),
 ("B_singletons_cost",Lean.toJson (additionalCost groupBs fbSingles)),("B_cheaper_cost",Lean.toJson (additionalCost groupBs fbCheap)),
 ("parent_singletons_cost",Lean.toJson (additionalCost groupSs (fa++fbSingles++fc))),
 ("parent_cheaper_cost",Lean.toJson (additionalCost groupSs (fa++fbCheap++fc))),
 ("B_internal_target_clear",Lean.toJson (pairwiseEmbeddings groupT [[3,5],[4,6]])),
 ("cross_group_clear",Lean.toJson (priorityBool groupT groupAs.head! groupBs groupCs)),
 ("source_permutation",Lean.toJson (decide (groupSs.Perm (groupAs++groupBs.reverse++groupCs)))),
 ("actual_sideOutputs_derived",Lean.toJson false),("recursive_solver_implemented",Lean.toJson false)]
#eval guard "local.A" (localTarget (some groupT) groupA) groupAs fa
#eval guard "local.C" (localTarget (some groupT) groupC) groupCs fc
#eval guard "local.Bsingletons" (localTarget (some groupT) groupB) groupBs fbSingles
#eval guard "local.Bcheaper" (localTarget (some groupT) groupB) groupBs fbCheap
-- Instrument-only supplied table. This definition does not assert ResidualSolverContract.
def mock (id : String) (q : Nat) (hasContract groupsOk : Bool) (answer : Option (List (List Nat))) : IO Unit := do
 let access := (q>0) && hasContract && groupsOk
 let fb := if access then answer else none
 let witness := fb.isSome
 let cost := fb.map (additionalCost groupBs)
 let total := fb.map (fun f => additionalCost groupSs (fa++f++fc))
 let checked := fb.all (fun f => agrees (localTarget (some groupT) groupB) groupBs f && decide (additionalCost groupBs f ≤ q-1) && agrees (some groupT) groupSs (fa++f++fc))
 if !checked then throw (IO.userError "mock supplied witness invalid")
 printObj id [("access",Lean.toJson access),("calls",Lean.toJson (if access then 1 else 0 : Nat)),
 ("child_budget",Lean.toJson (if access then some (q-1) else none)),("witness",Lean.toJson witness),
 ("child_cost",Lean.toJson cost),("parent_cost",Lean.toJson total)]

#eval mock "mock.q3_singletons" 3 true true (some [[3],[5],[4],[6]])

#eval mock "mock.q2_cheaper" 2 true true (some [[3,5],[4],[6]])

#eval mock "mock.q1_no_budget_completion" 1 true true (none)

#eval mock "mock.q0_no_call" 0 true true (none)

#eval mock "mock.missing_contract_no_access" 3 false true (none)

#eval mock "mock.invalid_group_ownership_no_access" 3 true false (none)

#check OutputState.checked_materialization
#check OutputState.sourceForest_proper
#check OutputState.exact_additional_cost
#check OutputState.agrees_iff_original
#check OutputState.generated_source_bridge
#check OutputState.opposite_grouping
#check OutputState.opposite_local_certificates
#check OutputState.every_opposite_residual_query
end FreshOutputReadouts
