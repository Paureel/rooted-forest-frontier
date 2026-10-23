import OwnershipBase

namespace Universal233.Assembly
open RMAF CoreProgram SourceCoverage VertexGeometry

theorem solution_from_requests (target source : Tree) (A B C : List Nat)
    (F : List (List Nat)) (a b c : Request) (q : Nat)
    (ht : (leaves target).Nodup) (hs : (leaves source).Nodup)
    (hlabels : ∀ x, x ∈ leaves source → x ∈ leaves target)
    (hf : agreement target source F = true)
    (hpp : partitionCheck (leaves source) [A,B,C] = true)
    (hab : ∀ x, x ∈ A → x ∈ B → False)
    (hac : ∀ x, x ∈ A → x ∈ C → False)
    (hbc : ∀ x, x ∈ B → x ∈ C → False)
    (hfp : RefinesBlocks F [A,B,C])
    (hia : ∀ z, z ∈ targets a → ¬selectedLeaves (leaves target) target z)
    (hib : ∀ z, z ∈ targets b → ¬selectedLeaves (leaves target) target z)
    (hic : ∀ z, z ∈ targets c → ¬selectedLeaves (leaves target) target z)
    (hca : ParentClears target F A a) (hcb : ParentClears target F B b)
    (hcc : ParentClears target F C c) (hq : F.length - 1 ≤ q) :
    BranchSolution target source A B C F q a b c := by
  have hpt : partitionCheck (leaves target) F = true := by
    have h := hf; simp only [agreement,Bool.and_eq_true] at h; exact h.1.1.1.1
  have hps : partitionCheck (leaves source) F = true := by
    have h := hf; simp only [agreement,Bool.and_eq_true] at h; exact h.1.1.1.2
  have hes : pairwiseEmbeddings source F = true := (agreement_graph_factors target source F hf).2.1
  exact requests_whole_source target source A B C F a b c q ht hs hlabels hpt hps hes hpp
    hab hac hbc hfp hia hib hic hca hcb hcc hq

/-- The joint middle call is one actual whole-source color/generator call,
not the union of two separately paid cuts in the same source parent. -/
theorem chain_actual_four_cover (target source : Tree) (A B C : List Nat)
    (F : List (List Nat)) (v w : RMAF.Vertex) (q : Nat)
    (ht : (leaves target).Nodup) (hs : (leaves source).Nodup)
    (hlabels : ∀ x, x ∈ leaves source → x ∈ leaves target)
    (hf : agreement target source F = true)
    (hpp : partitionCheck (leaves source) [A,B,C] = true)
    (hab : ∀ x, x ∈ A → x ∈ B → False)
    (hac : ∀ x, x ∈ A → x ∈ C → False)
    (hbc : ∀ x, x ∈ B → x ∈ C → False)
    (hfp : RefinesBlocks F [A,B,C])
    (hiv : ¬selectedLeaves (leaves target) target v)
    (hiw : ¬selectedLeaves (leaves target) target w) (hq : F.length - 1 ≤ q) :
    BranchSolution target source A B C F q .keep (.at v) (.at w) ∨
    BranchSolution target source A B C F q .keep (.both v w) .keep ∨
    BranchSolution target source A B C F q (.at v) .keep (.at w) ∨
    BranchSolution target source A B C F q (.at v) (.at w) .keep := by
  have build := solution_from_requests target source A B C F
  have own := executable_chain_four_cover target source F (parentGroups F A B) v w hf
    (parentGroups_belongs F A B) (parentGroups_disjoint F A B)
  rcases own with ⟨cb,cc⟩ | ⟨cbv,cbw⟩ | ⟨ca,cc⟩ | ⟨ca,cb⟩
  · exact Or.inl (build .keep (.at v) (.at w) q ht hs hlabels hf hpp hab hac hbc hfp
      (internal_keep target) (internal_at target v hiv) (internal_at target w hiw)
      (keeps_clear target F A) (clears_B target F A B v hab cb)
      (clears_C target F A B C w hac hbc cc) hq)
  · exact Or.inr (Or.inl (build .keep (.both v w) .keep q ht hs hlabels hf hpp hab hac hbc hfp
      (internal_keep target) (internal_both target v w hiv hiw) (internal_keep target)
      (keeps_clear target F A) (both_clear target F B v w
        (clears_B target F A B v hab cbv) (clears_B target F A B w hab cbw))
      (keeps_clear target F C) hq))
  · exact Or.inr (Or.inr (Or.inl (build (.at v) .keep (.at w) q ht hs hlabels hf hpp hab hac hbc hfp
      (internal_at target v hiv) (internal_keep target) (internal_at target w hiw)
      (clears_A target F A B v ca) (keeps_clear target F B)
      (clears_C target F A B C w hac hbc cc) hq)))
  · exact Or.inr (Or.inr (Or.inr (build (.at v) (.at w) .keep q ht hs hlabels hf hpp hab hac hbc hfp
      (internal_at target v hiv) (internal_at target w hiw) (internal_keep target)
      (clears_A target F A B v ca) (clears_B target F A B w hab cb)
      (keeps_clear target F C) hq)))

/-- Exactly-two middle regions use the paid diagonal ownership cover: clear
B once jointly OR clear the two distinct outer parents. -/
theorem chain_actual_diagonal_cover (target source : Tree) (A B C : List Nat)
    (F : List (List Nat)) (v w : RMAF.Vertex) (q : Nat)
    (ht : (leaves target).Nodup) (hs : (leaves source).Nodup)
    (hlabels : ∀ x, x ∈ leaves source → x ∈ leaves target)
    (hf : agreement target source F = true)
    (hpp : partitionCheck (leaves source) [A,B,C] = true)
    (hab : ∀ x, x ∈ A → x ∈ B → False)
    (hac : ∀ x, x ∈ A → x ∈ C → False)
    (hbc : ∀ x, x ∈ B → x ∈ C → False)
    (hfp : RefinesBlocks F [A,B,C])
    (hiv : ¬selectedLeaves (leaves target) target v)
    (hiw : ¬selectedLeaves (leaves target) target w)
    (hv : v ∈ minimalVertices B target) (hw : w ∈ minimalVertices B target)
    (hjoint : (jointColors B target v w).length = 2) (hq : F.length - 1 ≤ q) :
    BranchSolution target source A B C F q .keep (.both v w) .keep ∨
    BranchSolution target source A B C F q (.at v) .keep (.at w) := by
  have hBlabs : ∀ x, x ∈ B → x ∈ leaves target := by
    intro x hx
    exact hlabels x (partitionCheck_subset _ [A,B,C] hpp (List.mem_flatten.mpr ⟨B,by simp,hx⟩))
  have hBv : ¬selectedLeaves B target v := by
    intro h
    exact hiv (selected_leaves_mono B (leaves target) target hBlabs v h)
  have hBw : ¬selectedLeaves B target w := by
    intro h
    exact hiw (selected_leaves_mono B (leaves target) target hBlabs w h)
  have own := executable_chain_paid_cover target source F (parentGroups F A B) B v w hf
    (parentGroups_belongs F A B) (parentGroups_disjoint F A B)
    (fun b hb => parentGroups_1_subset_B F A B b hb) hBv hBw hv hw hjoint
  have build := solution_from_requests target source A B C F
  rcases own with ⟨cbv,cbw⟩ | ⟨ca,cc⟩
  · exact Or.inl (build .keep (.both v w) .keep q ht hs hlabels hf hpp hab hac hbc hfp
      (internal_keep target) (internal_both target v w hiv hiw) (internal_keep target)
      (keeps_clear target F A) (both_clear target F B v w
        (clears_B target F A B v hab cbv) (clears_B target F A B w hab cbw))
      (keeps_clear target F C) hq)
  · exact Or.inr (build (.at v) .keep (.at w) q ht hs hlabels hf hpp hab hac hbc hfp
      (internal_at target v hiv) (internal_keep target) (internal_at target w hiw)
      (clears_A target F A B v ca) (keeps_clear target F B)
      (clears_C target F A B C w hac hbc cc) hq)

end Universal233.Assembly
