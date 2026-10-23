import CoreInvariants
open RMAF Universal233.CoreProgram Universal233.CoreProgram.Controls

-- Fresh operational predictions from rule order and instrument definitions.
example : let r := generate crossed parity 0
    (r.visited, r.childAttempts, r.pruned, r.outputs.length) = (1, 2, 2, 0) := by decide
example : let r := generate crossed parity 1
    (r.visited, r.childAttempts, r.pruned, r.outputs.length) = (3, 4, 2, 0) := by decide
example : let r := generate crossed parity 2
    (r.visited, r.childAttempts, r.pruned, r.outputs.length) = (5, 4, 0, 2) := by decide
example : let r := generate crossed parity 3
    (r.visited, r.childAttempts, r.pruned, r.outputs.length) = (5, 4, 0, 2) := by decide
example : let r := attempt (fun _ _ _ => ⟨[],[],0,0,1⟩) (fromTree id [] (.leaf 7)) [] [] ⟨[],[7],7⟩
    (r.visited, r.childAttempts, r.pruned, r.refusals.length) = (0,1,0,1) := by decide
example : let r := attempt (fun _ _ _ => ⟨[],[],0,0,1⟩) (fromTree id [] (.node (.leaf 0) (.leaf 1))) [] [[false]] ⟨[false],[0],0⟩
    (r.visited, r.childAttempts, r.pruned, r.refusals.length) = (0,1,0,1) := by decide
example : let r := attempt (fun _ _ _ => ⟨[],[],0,0,1⟩) (GTree.leaf ⟨[false],[0],0⟩) [] [] ⟨[false],[0],0⟩
    (r.visited, r.childAttempts, r.pruned, r.refusals.length) = (0,1,0,1) := by decide

-- GoodCuts and OutputShape really permit this nonexistent endpoint.
def fake : Output := ⟨[[0],[1,2]], [[false,false,false]]⟩
example : GoodCuts fake.sourceCuts := by simp [GoodCuts, fake]
example : OutputShape fake := by unfold OutputShape fake; decide
example : ¬ Universal233.CoreGraph.Valid cherry3 [false,false,false] := by
  intro h
  rcases h with ⟨s, hs⟩
  simp [Universal233.CoreGraph.subtree, cherry3] at hs

#print axioms run_visited_exponential
#print axioms run_attempts_bound
#print axioms run_prefix_work_bound
#print axioms generate_cut_records
#print axioms generate_recorded_charge
