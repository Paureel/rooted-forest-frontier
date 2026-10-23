import Materialize
namespace OutputState
open RMAF RestrictionBridge ForestState

theorem source_topology (T S s : Tree) (U B : List Nat)
    (hs : restrict U S = some s) (sub : B ⊆ U) :
    targetAgrees (some T) s B = restrictionAgrees T S B := by
  simp only [targetAgrees,restrictionAgrees,restrict_inside S s U B hs sub]

theorem source_forward (T S : Tree) (Q F : List (List Nat))
    (properS : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true)
    (ha : agreement T S F = true) (href : Refines F Q) :
    ∀ s ∈ sourceForest S Q, sourceCheck (some T) F s = true := by
  have hh := ha
  simp only [agreement,Bool.and_eq_true] at hh
  intro s hm
  obtain ⟨U,hU,hs⟩ := (source_component S Q s).1 hm
  have hl := component_labels S s U Q hs properS hQ hU
  have hf := family_members (leaves s) U F (fun x => hl.mem_iff)
  simp only [sourceCheck,hf,Bool.and_eq_true]
  refine ⟨⟨local_partition S s U F Q hs hh.1.1.1.2 hQ href hU,?_⟩,?_⟩
  · apply List.all_eq_true.2
    intro B hB
    obtain ⟨hBF,hBU⟩ := (mem_family B U F).1 hB
    rw [source_topology T S s U B hs hBU]
    exact List.all_eq_true.1 hh.1.1.2 B hBF
  · exact (pairwise_transport S s U (family U F) hs (fun B hB => ((mem_family B U F).1 hB).2)).1
      (pairwise_filter S F (contained · U) hh.2)

theorem original_to_state (T S : Tree) (Q F : List (List Nat))
    (properT : (leaves T).Nodup) (properS : (leaves S).Nodup)
    (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
    (hQ : partitionCheck (leaves S) Q = true)
    (ha : agreement T S F = true) (href : Refines F Q) :
    agrees (some T) (sourceForest S Q) F = true := by
  have hh := ha
  simp only [agreement,Bool.and_eq_true] at hh
  simp only [agrees,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,contained_iff]
  refine ⟨⟨⟨⟨sourceForest_proper T S Q properT properS same hQ,hh.1.1.1.1⟩,?_⟩,hh.1.2⟩,
    source_forward T S Q F properS hQ ha href⟩
  intro B hB
  obtain ⟨U,hU,hBU⟩ := href B hB
  obtain ⟨s,hs,hl⟩ := checked_restrictions S Q properS hQ U hU
  exact ⟨s,(source_component S Q s).2 ⟨U,hU,hs⟩,fun x hx => hl.mem_iff.2 (hBU hx)⟩

theorem state_refinement (T S : Tree) (Q F : List (List Nat))
    (properS : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true)
    (ha : agrees (some T) (sourceForest S Q) F = true) : Refines F Q := by
  intro B hB
  obtain ⟨s,hs,hBs⟩ := (agrees_parts _ _ _ ha).2.2.1 B hB
  obtain ⟨U,hU,hr⟩ := (source_component S Q s).1 hs
  have hl := component_labels S s U Q hr properS hQ hU
  exact ⟨U,hU,fun x hx => hl.mem_iff.1 (hBs hx)⟩

theorem source_reverse_local (T S : Tree) (Q F : List (List Nat))
    (properS : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true)
    (ha : agrees (some T) (sourceForest S Q) F = true) :
    ∀ U ∈ Q, pairwiseEmbeddings S (family U F) = true := by
  intro U hU
  obtain ⟨s,hs,hl⟩ := checked_restrictions S Q properS hQ U hU
  have hm := (source_component S Q s).2 ⟨U,hU,hs⟩
  have hc := (agrees_parts _ _ _ ha).2.2.2.2 s hm
  have hf := family_members (leaves s) U F (fun x => hl.mem_iff)
  simp only [sourceCheck,hf,Bool.and_eq_true] at hc
  exact (pairwise_transport S s U (family U F) hs (fun B hB => ((mem_family B U F).1 hB).2)).2 hc.2

theorem source_reverse_global (T S : Tree) (Q F : List (List Nat))
    (properS : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true)
    (sourceQ : pairwiseEmbeddings S Q = true)
    (ha : agrees (some T) (sourceForest S Q) F = true) :
    pairwiseEmbeddings S F = true := by
  obtain ⟨hp,hF,hcontains,hEt,hchecks⟩ := agrees_parts _ _ _ ha
  have href := state_refinement T S Q F properS hQ ha
  have locals := source_reverse_local T S Q F properS hQ ha
  apply (pairwise_iff S F).2
  apply List.Pairwise.imp_of_mem (R := fun B C => B ≠ C) (S := fun B C => Clear (minimalVertices B S) (minimalVertices C S))
      (p := checked_family_nodup (leaves T) F hF)
  intro B C hB hC hne
  obtain ⟨U,hU,hBU⟩ := href B hB
  obtain ⟨V,hV,hCV⟩ := href C hC
  by_cases huv : U = V
  · subst V
    exact pairwise_distinct S (family U F) (locals U hU) B C
      ((mem_family B U F).2 ⟨hB,hBU⟩) ((mem_family C U F).2 ⟨hC,hCV⟩) hne
  · exact cross_subblocks S Q sourceQ U V B C hU hV huv hBU hCV

theorem state_to_original (T S : Tree) (Q F : List (List Nat))
    (properS : (leaves S).Nodup)
    (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
    (hQ : partitionCheck (leaves S) Q = true)
    (sourceQ : pairwiseEmbeddings S Q = true)
    (ha : agrees (some T) (sourceForest S Q) F = true) :
    agreement T S F = true ∧ Refines F Q := by
  obtain ⟨hp,hF,hcontains,hEt,hchecks⟩ := agrees_parts _ _ _ ha
  refine ⟨?_,state_refinement T S Q F properS hQ ha⟩
  simp only [agreement,Bool.and_eq_true]
  refine ⟨⟨⟨⟨hF,(partition_labels_congr _ _ F same).1 hF⟩,?_⟩,hEt⟩,
    source_reverse_global T S Q F properS hQ sourceQ ha⟩
  apply List.all_eq_true.2
  intro B hB
  obtain ⟨s,hs,hBs⟩ := hcontains B hB
  obtain ⟨U,hU,hr⟩ := (source_component S Q s).1 hs
  have hl := component_labels S s U Q hr properS hQ hU
  have sub : B ⊆ U := fun x hx => hl.mem_iff.1 (hBs hx)
  have hc := hchecks s hs
  simp only [sourceCheck,Bool.and_eq_true] at hc
  rw [←source_topology T S s U B hr sub]
  exact List.all_eq_true.1 hc.1.2 B ((mem_family B (leaves s) F).2 ⟨hB,hBs⟩)

/-- Literal equivalence for arbitrary actual label/block order. Q needs original
SOURCE embeddings; no target-Q embedding hypothesis occurs. -/
theorem agrees_iff_original (T S : Tree) (Q F : List (List Nat))
    (properT : (leaves T).Nodup) (properS : (leaves S).Nodup)
    (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
    (hQ : partitionCheck (leaves S) Q = true)
    (sourceQ : pairwiseEmbeddings S Q = true) :
    agrees (some T) (sourceForest S Q) F = true ↔
      agreement T S F = true ∧ Refines F Q := by
  constructor
  · exact state_to_original T S Q F properS same hQ sourceQ
  · rintro ⟨ha,href⟩
    exact original_to_state T S Q F properT properS same hQ ha href
end OutputState
