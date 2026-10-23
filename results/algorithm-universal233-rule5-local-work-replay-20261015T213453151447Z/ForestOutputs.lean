import SourceValidity

namespace Universal233.Assembly
open RMAF CoreProgram SourceCoverage VertexGeometry

theorem parent_partition_disjoint (S : Tree) (A B C : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true) :
    (∀ x, x ∈ A → x ∈ B → False) ∧
    (∀ x, x ∈ A → x ∈ C → False) ∧
    (∀ x, x ∈ B → x ∈ C → False) := by
  have hc : (leaves S).all (fun x => [A,B,C].flatten.count x == 1) = true := by
    simp only [partitionCheck,Bool.and_eq_true] at hp
    exact hp.1.2
  have countOne : ∀ x, x ∈ A ∨ x ∈ B ∨ x ∈ C → A.count x + B.count x + C.count x = 1 := by
    intro x hx
    have hf : x ∈ [A,B,C].flatten := by simpa using hx
    have hs := partitionCheck_subset _ [A,B,C] hp hf
    have h := beq_iff_eq.mp (List.all_eq_true.mp hc x hs)
    simpa [List.count_append,Nat.add_assoc] using h
  refine ⟨?_,?_,?_⟩
  · intro x ha hb
    have a := List.count_pos_iff.mpr ha
    have b := List.count_pos_iff.mpr hb
    have h := countOne x (Or.inl ha)
    omega
  · intro x ha hc
    have a := List.count_pos_iff.mpr ha
    have c := List.count_pos_iff.mpr hc
    have h := countOne x (Or.inl ha)
    omega
  · intro x hb hc
    have b := List.count_pos_iff.mpr hb
    have c := List.count_pos_iff.mpr hc
    have h := countOne x (Or.inr (Or.inl hb))
    omega

def ForestBranchSolution (target source : Tree) (A B C : List Nat) (F : List (List Nat))
    (q : Nat) (a b c : Request) : Prop :=
    ∃ o, o ∈ (generate source (requestedColor target A B a b c) q).outputs ∧
      RefinesBlocks F o.partition ∧ RefinesBlocks o.partition [A,B,C] ∧
      partitionCheck (leaves source) o.partition = true ∧ pairwiseEmbeddings source o.partition = true ∧
      CutRealization.RealizedOutput source o ∧ o.sourceCuts.length ≤ q ∧
      ParentClears target o.partition A a ∧ ParentClears target o.partition B b ∧
      ParentClears target o.partition C c

theorem branch_is_source_forest {target source A B C F q a b c}
    (h : BranchSolution target source A B C F q a b c) :
    ForestBranchSolution target source A B C F q a b c := by
  obtain ⟨o,ho,href,hparents,hpart,hreal,hbudget,ha,hb,hc⟩ := h
  exact ⟨o,ho,href,hparents,hpart,(generated_source_valid source _ q o ho).2,hreal,hbudget,ha,hb,hc⟩

/-- Consuming clique constructor: source-parent disjointness comes from the
actual original partition checker, and every returned child is source-valid. -/
theorem clique_forest_cover (target source : Tree) (A B C : List Nat)
    (F : List (List Nat)) (v : RMAF.Vertex) (q : Nat)
    (ht : (leaves target).Nodup) (hs : (leaves source).Nodup)
    (hlabels : ∀ x, x ∈ leaves source → x ∈ leaves target)
    (hf : agreement target source F = true)
    (hpp : partitionCheck (leaves source) [A,B,C] = true)
    (hfp : RefinesBlocks F [A,B,C])
    (hi : ¬selectedLeaves (leaves target) target v) (hq : F.length - 1 ≤ q) :
    ForestBranchSolution target source A B C F q .keep (.at v) (.at v) ∨
    ForestBranchSolution target source A B C F q (.at v) .keep (.at v) ∨
    ForestBranchSolution target source A B C F q (.at v) (.at v) .keep := by
  obtain ⟨hab,hac,hbc⟩ := parent_partition_disjoint source A B C hpp
  rcases clique_actual_cover target source A B C F v q ht hs hlabels hf hpp hab hac hbc hfp hi hq with h | h | h
  · exact Or.inl (branch_is_source_forest h)
  · exact Or.inr (Or.inl (branch_is_source_forest h))
  · exact Or.inr (Or.inr (branch_is_source_forest h))

theorem chain_forest_four_cover (target source : Tree) (A B C : List Nat)
    (F : List (List Nat)) (v w : RMAF.Vertex) (q : Nat)
    (ht : (leaves target).Nodup) (hs : (leaves source).Nodup)
    (hlabels : ∀ x, x ∈ leaves source → x ∈ leaves target)
    (hf : agreement target source F = true)
    (hpp : partitionCheck (leaves source) [A,B,C] = true)
    (hfp : RefinesBlocks F [A,B,C])
    (hiv : ¬selectedLeaves (leaves target) target v)
    (hiw : ¬selectedLeaves (leaves target) target w) (hq : F.length - 1 ≤ q) :
    ForestBranchSolution target source A B C F q .keep (.at v) (.at w) ∨
    ForestBranchSolution target source A B C F q .keep (.both v w) .keep ∨
    ForestBranchSolution target source A B C F q (.at v) .keep (.at w) ∨
    ForestBranchSolution target source A B C F q (.at v) (.at w) .keep := by
  obtain ⟨hab,hac,hbc⟩ := parent_partition_disjoint source A B C hpp
  rcases chain_actual_four_cover target source A B C F v w q ht hs hlabels hf hpp hab hac hbc hfp hiv hiw hq with h | h | h | h
  · exact Or.inl (branch_is_source_forest h)
  · exact Or.inr (Or.inl (branch_is_source_forest h))
  · exact Or.inr (Or.inr (Or.inl (branch_is_source_forest h)))
  · exact Or.inr (Or.inr (Or.inr (branch_is_source_forest h)))

theorem chain_forest_diagonal_cover (target source : Tree) (A B C : List Nat)
    (F : List (List Nat)) (v w : RMAF.Vertex) (q : Nat)
    (ht : (leaves target).Nodup) (hs : (leaves source).Nodup)
    (hlabels : ∀ x, x ∈ leaves source → x ∈ leaves target)
    (hf : agreement target source F = true)
    (hpp : partitionCheck (leaves source) [A,B,C] = true)
    (hfp : RefinesBlocks F [A,B,C])
    (hiv : ¬selectedLeaves (leaves target) target v)
    (hiw : ¬selectedLeaves (leaves target) target w)
    (hv : v ∈ minimalVertices B target) (hw : w ∈ minimalVertices B target)
    (hjoint : (jointColors B target v w).length = 2) (hq : F.length - 1 ≤ q) :
    ForestBranchSolution target source A B C F q .keep (.both v w) .keep ∨
    ForestBranchSolution target source A B C F q (.at v) .keep (.at w) := by
  obtain ⟨hab,hac,hbc⟩ := parent_partition_disjoint source A B C hpp
  rcases chain_actual_diagonal_cover target source A B C F v w q ht hs hlabels hf hpp hab hac hbc hfp hiv hiw hv hw hjoint hq with h | h
  · exact Or.inl (branch_is_source_forest h)
  · exact Or.inr (branch_is_source_forest h)

end Universal233.Assembly
