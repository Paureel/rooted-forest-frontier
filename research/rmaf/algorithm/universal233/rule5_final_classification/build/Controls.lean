import Unordered
import PreControls
namespace Universal233.CherryBranching.Controls
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent
open Universal233.CherryBranching.Pre

theorem control_t3_literal : pendantPartition s3 0 1 = [[2],[3],[4],[0,1]] := by decide
theorem control_t1_literal : pendantPartition s1 0 1 = [[2],[0,1]] := by decide
theorem control_t1_failure : ¬Refines [[0,2],[1]] (pendantPartition s1 0 1) := by
 intro h
 obtain ⟨B,hB,hsub⟩ := h [0,2] (by simp)
 have h0 := hsub 0 (by simp)
 have h2 := hsub 2 (by simp)
 have hc : B = [2] ∨ B = [0,1] := by simpa [control_t1_literal] using hB
 rcases hc with rfl | rfl <;> simp_all

theorem control_t1_exchange : agreement t1 s1 [[0,1],[2]] = true ∧
 ([[0,1],[2]] : List (List Nat)).length ≤ [[0,2],[1]].length ∧
 Refines [[0,1],[2]] (pendantPartition s1 0 1) := by
 refine ⟨by decide,by decide,?_⟩
 intro B hB
 have hc : B = [0,1] ∨ B = [2] := by simpa using hB
 rcases hc with rfl | rfl
 · exact ⟨[0,1],by simp [control_t1_literal],fun _ h => h⟩
 · exact ⟨[2],by simp [control_t1_literal],fun _ h => h⟩

theorem control_endpoint_cut : terminalCut s3 0 = some [false,false,false] := by decide
theorem control_endpoint_paid : (singletonChild s3 0).paid = 1 := by decide
theorem control_high_paid : (pendantChild s3 0 1).paid = 3 := by decide
theorem control_high_materialization : (pendantChild s3 0 1).sourceForest =
 [.leaf 2,.leaf 3,.leaf 4,.node (.leaf 0) (.leaf 1)] := by decide
theorem control_one_priority : (select t1 s1).map Prod.fst = some .one := by decide
theorem control_high_priority : (select t3 s3).map Prod.fst = some .high := by decide
theorem control_upward_labels : pendantPartition s3up 0 1 = [[2],[3],[4],[0,1,5]] := by decide
theorem control_underpaid_refused : remaining 2 (pendantChild s3 0 1) = none := by decide
theorem control_exact_budget : remaining 5 (pendantChild s3 0 1) = some 2 := by decide
theorem control_t1_universal_call : ∃ G, agreement t1 s1 G = true ∧
 G.length ≤ ([[0,2],[1]] : List (List Nat)).length ∧ Refines G (pendantPartition s1 0 1) := by
 exact actual_t1_pendant_exchange (by decide) (by decide)
   (by intro x; simp [t1,s1,leaves,or_assoc,or_comm,or_left_comm])
   (by decide) (p:=[false]) (by rfl) (by decide)

theorem control_t1_root_boundary_call : ∃ G,
 agreement (.node t1 (.leaf 5)) (.node s1 (.leaf 5)) G = true ∧
 G.length ≤ ([[0,2],[1],[5]] : List (List Nat)).length ∧
 Refines G (pendantPartition (.node s1 (.leaf 5)) 0 1) := by
 exact actual_t1_pendant_exchange (by decide) (by decide)
   (by intro x; simp [t1,s1,leaves,or_assoc,or_comm,or_left_comm])
   (by decide) (p:=[false,false]) (by rfl) (by decide)

private theorem internal_control : (highBranch s3 0 1).originalCuts.length = 3 := by decide
end Universal233.CherryBranching.Controls
