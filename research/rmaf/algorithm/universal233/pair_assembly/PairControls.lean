import GoodPair
import PairPrecontrols

namespace Universal233.PairAssembly.Controls
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PaidAssembly

theorem refines_of_check (F Q : List (List Nat)) (h : refinesBool F Q = true) : RefinesBlocks F Q := by
  intro K hK
  obtain ⟨U,hU,hKU⟩ := List.any_eq_true.1 (List.all_eq_true.1 h K hK)
  exact ⟨U,hU,fun x hx => List.contains_iff_mem.1 (List.all_eq_true.1 hKU x hx)⟩

theorem same_labels : ∀ x, x ∈ leaves s ↔ x ∈ leaves t := by
  intro x; simp [s,t,leaves,or_comm,or_left_comm]

theorem t1_outside_clear : ∀ E, E ∈ [a,b,c] → E ≠ a → E ≠ b → Disj t E a ∧ Disj t E b := by
  intro E hE hEA hEB
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hE
  rcases hE with hE | hE | rfl
  · exact False.elim (hEA hE)
  · exact False.elim (hEB hE)
  · exact ⟨(executable_disjointVertices t c a).1 (by decide),
      (executable_disjointVertices t c b).1 (by decide)⟩

theorem control_total_good_pair :
    (∃ F' o choice, PairGeometry.choose t a b = some choice ∧ agreement s t F' = true ∧
      F'.length ≤ originalF.length ∧ RefinesBlocks F' [a,b,c] ∧ o ∈ goodPairOutputs s t a b 6 ∧
      OutputWitness s [a,b,c] F' 6 o ∧ ChoiceProgress s t a b o choice) ∧
    rawQMass (mkRat 233 100) (goodPairOutputs s t a b 6) ≤
      (mkRat 233 100)^(-3 : Int)+(mkRat 233 100)^(-4 : Int) := by
  exact good_pair_cover_mass s t a b c originalF 6 (by decide) (by decide) same_labels
    (by decide) (by decide) (by decide) ⟨[false],by decide,by decide⟩ t1_outside_clear
    (by decide) control_original_exchange_agreements.1 (refines_of_check _ _ (by decide)) (by decide)
    (mkRat 233 100) (by decide)

theorem control_all_literal_B_outputs_clear_A : ∀ o, o ∈ sideOutputs s a b d 6 →
    ∀ K, K ∈ o.partition → Sub K b → Disj t K a := by
  intro o ho
  exact side_output_clear s t a b c d 6 o ho (by decide)
    ((executable_disjointVertices t (yes b (d.contains ·)) a).1 (by decide))
    ((executable_disjointVertices t (no b (d.contains ·)) a).1 (by decide))

def vertexT : Tree := .node (.node (.node (.leaf 0) (.leaf 3)) (.node (.leaf 1) (.node (.leaf 2) (.leaf 4)))) (.leaf 5)
def vertexS : Tree := .node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5))

theorem control_actual_three_vertex : PairGeometry.choose vertexT [0,1,2] [3,4] = some (.vertex [false,true]) := by decide

theorem control_three_vertex_mass :
    rawQMass (mkRat 233 100) (vertexPairOutputs vertexS vertexT [0,1,2] [3,4] [false,true] 5) ≤
      (mkRat 233 100)^(-3 : Int)+(mkRat 233 100)^(-4 : Int) := by
  have hl : ∀ x, x ∈ leaves vertexS → x ∈ leaves vertexT := by
    intro x hx; simpa [vertexS,vertexT,leaves,or_assoc,or_comm,or_left_comm] using hx
  exact vertex_pair_three_mass vertexS vertexT [0,1,2] [3,4] [5] [false,true]
    (by decide) hl (by decide) (by decide) (by decide) (Or.inl (by decide)) 5 (mkRat 233 100) (by decide)

theorem control_hard_parents_actual_source_forest :
    pairwiseEmbeddings HardParent.source4 [[2],[3],[0,1]] = true := by
  have h := HardParent.actual_hard2_named_safety (by decide) HardParent.control_clean_agreement
    (p := [false]) (a := 0) (b := 1) rfl HardParent.control_root_lca_cuts
  exact hard_parent_embeddings (by decide) h.1

private theorem origin_control : (mkRat 233 100) ≥ 2 := by decide
theorem control_private_origin : (mkRat 233 100) ≥ 2 := origin_control
end Universal233.PairAssembly.Controls
