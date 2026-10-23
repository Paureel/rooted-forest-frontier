import GroupCost

namespace RestrictionBridge
open RMAF

theorem partition_labels_congr (L M : List Nat) (F : List (List Nat))
    (he : ∀ x, x ∈ L ↔ x ∈ M) :
    partitionCheck L F = true ↔ partitionCheck M F = true := by
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem]
  constructor
  · rintro ⟨⟨hn,hc⟩,hl⟩
    exact ⟨⟨hn,fun x hx => hc x ((he x).2 hx)⟩,fun x hx => (he x).1 (hl x hx)⟩
  · rintro ⟨⟨hn,hc⟩,hl⟩
    exact ⟨⟨hn,fun x hx => hc x ((he x).1 hx)⟩,fun x hx => (he x).2 (hl x hx)⟩

theorem checked_block_nodup (L : List Nat) (Q : List (List Nat))
    (hQ : partitionCheck L Q = true) (U : List Nat) (hU : U ∈ Q) : U.Nodup := by
  apply List.nodup_iff_count.2
  intro x
  by_cases hx : x ∈ U
  · have hc := checked_count L Q hQ (checked_label L Q hQ hU hx)
    have hle := (List.sublist_flatten_of_mem hU).count_le x
    omega
  · simp [List.count_eq_zero.2 hx]

theorem component_labels (t u : Tree) (U : List Nat) (Q : List (List Nat))
    (hr : restrict U t = some u) (proper : (leaves t).Nodup)
    (hQ : partitionCheck (leaves t) Q = true) (hU : U ∈ Q) : (leaves u).Perm U := by
  apply (List.perm_ext_iff_of_nodup (restricted_nodup t u U hr proper)
    (checked_block_nodup (leaves t) Q hQ U hU)).2
  intro x
  rw [restricted_labels_exact t u U hr]
  exact ⟨And.right,fun hx => ⟨checked_label (leaves t) Q hQ hU hx,hx⟩⟩

theorem pairwise_filter (t : Tree) (F : List (List Nat)) (p : List Nat → Bool)
    (h : pairwiseEmbeddings t F = true) : pairwiseEmbeddings t (F.filter p) = true := by
  induction F with
  | nil => simp [pairwiseEmbeddings]
  | cons B F ih =>
    simp only [pairwiseEmbeddings,Bool.and_eq_true] at h
    cases hp : p B with
    | false => simpa [List.filter_cons,hp] using ih h.2
    | true =>
      simp only [List.filter_cons,hp,↓reduceIte,pairwiseEmbeddings,Bool.and_eq_true]
      refine ⟨List.all_eq_true.2 ?_,ih h.2⟩
      intro C hc
      exact List.all_eq_true.1 h.1 C (List.mem_filter.1 hc).1

theorem forward_local (T S t s : Tree) (F Q : List (List Nat)) (U : List Nat)
    (ha : agreement T S F = true) (hQ : partitionCheck (leaves S) Q = true)
    (href : Refines F Q) (hU : U ∈ Q)
    (ht : restrict U T = some t) (hs : restrict U S = some s) :
    agreement t s (family U F) = true := by
  have hh := ha
  simp only [agreement,Bool.and_eq_true] at hh
  have hpT := hh.1.1.1.1
  have hpS := hh.1.1.1.2
  have labels := checked_labels_iff (leaves T) (leaves S) F hpT hpS
  have hQT := (partition_labels_congr (leaves T) (leaves S) Q labels).2 hQ
  have hsub : ∀ B ∈ family U F, B ⊆ U := fun B hB => ((mem_family B U F).1 hB).2
  have hEt := pairwise_filter T F (contained · U) hh.1.2
  have hEs := pairwise_filter S F (contained · U) hh.2
  simp only [agreement,Bool.and_eq_true]
  refine ⟨⟨⟨⟨local_partition T t U F Q ht hpT hQT href hU,
    local_partition S s U F Q hs hpS hQ href hU⟩,?_⟩,?_⟩,?_⟩
  · apply List.all_eq_true.2
    intro B hB
    obtain ⟨hBF,hBU⟩ := (mem_family B U F).1 hB
    rw [sameShape_restrict_inside T S t s U B ht hs hBU]
    exact List.all_eq_true.1 hh.1.1.2 B hBF
  · exact (pairwise_transport T t U (family U F) ht hsub).1 hEt
  · exact (pairwise_transport S s U (family U F) hs hsub).1 hEs

/-- Actual original agreement, literal filtered families, proper original labels,
and exact additive cost. Q is only a checked partition and need not agree. -/
theorem forward_decomposition (T S : Tree) (F Q : List (List Nat))
    (properT : (leaves T).Nodup) (properS : (leaves S).Nodup)
    (ha : agreement T S F = true) (hQ : partitionCheck (leaves S) Q = true)
    (href : Refines F Q) :
    (∀ U ∈ Q, ∃ t s, restrict U T = some t ∧ restrict U S = some s ∧
      (leaves t).Perm U ∧ (leaves s).Perm U ∧ agreement t s (family U F) = true) ∧
    (Q.map (fun U => (family U F).length - 1)).sum = F.length - Q.length := by
  have hh := ha
  simp only [agreement,Bool.and_eq_true] at hh
  have hpT := hh.1.1.1.1
  have hpS := hh.1.1.1.2
  have labels := checked_labels_iff (leaves T) (leaves S) F hpT hpS
  have hQT := (partition_labels_congr (leaves T) (leaves S) Q labels).2 hQ
  refine ⟨?_,exact_cost (leaves S) F Q hpS hQ href⟩
  intro U hU
  have hn := checked_nonempty (leaves S) Q hQ U hU
  obtain ⟨x,hx⟩ : ∃ x, x ∈ U := List.exists_mem_of_ne_nil U hn
  have hxS := checked_label (leaves S) Q hQ hU hx
  obtain ⟨t,ht⟩ := restriction_exists T U ⟨x,(labels x).2 hxS,hx⟩
  obtain ⟨s,hs⟩ := restriction_exists S U ⟨x,hxS,hx⟩
  exact ⟨t,s,ht,hs,component_labels T t U Q ht properT hQT hU,
    component_labels S s U Q hs properS hQ hU,forward_local T S t s F Q U ha hQ href hU ht hs⟩

end RestrictionBridge
