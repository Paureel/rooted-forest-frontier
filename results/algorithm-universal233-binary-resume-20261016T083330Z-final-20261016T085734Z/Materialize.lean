import OutputDefs
namespace OutputState
open RMAF RestrictionBridge ForestState

theorem source_component (S : Tree) (Q : List (List Nat)) (s : Tree) :
    s ∈ sourceForest S Q ↔ ∃ U ∈ Q, restrict U S = some s := by
  simp [sourceForest,List.mem_filterMap]

theorem checked_restrictions (S : Tree) (Q : List (List Nat))
    (properS : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true) :
    ∀ U ∈ Q, ∃ s, restrict U S = some s ∧ (leaves s).Perm U := by
  intro U hU
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil U (checked_nonempty _ _ hQ U hU)
  obtain ⟨s,hs⟩ := restriction_exists S U ⟨x,checked_label _ _ hQ hU hx,hx⟩
  exact ⟨s,hs,component_labels S s U Q hs properS hQ hU⟩

theorem materialized_length (S : Tree) (Q : List (List Nat))
    (all : ∀ U ∈ Q, ∃ s, restrict U S = some s) :
    (sourceForest S Q).length = Q.length := by
  induction Q with
  | nil => rfl
  | cons U Q ih =>
    obtain ⟨s,hs⟩ := all U (by simp)
    simpa [sourceForest,hs] using congrArg Nat.succ (ih (fun V hv => all V (by simp [hv])))

theorem materialized_flatten (S : Tree) (Q : List (List Nat))
    (all : ∀ U ∈ Q, ∃ s, restrict U S = some s ∧ (leaves s).Perm U) :
    ((sourceForest S Q).map leaves).flatten.Perm Q.flatten := by
  induction Q with
  | nil => exact .refl []
  | cons U Q ih =>
    obtain ⟨s,hs,hl⟩ := all U (by simp)
    simpa [sourceForest,hs] using hl.append (ih (fun V hv => all V (by simp [hv])))

theorem checked_materialization (S : Tree) (Q : List (List Nat))
    (properS : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true) :
    (sourceForest S Q).length = Q.length ∧
    ((sourceForest S Q).map leaves).flatten.Perm Q.flatten ∧
    (∀ s ∈ sourceForest S Q, ∃ U ∈ Q, restrict U S = some s ∧
      (leaves s).Perm U ∧ (leaves s).Nodup ∧ leaves s ≠ []) := by
  have all := checked_restrictions S Q properS hQ
  refine ⟨materialized_length S Q (fun U hU => let ⟨s,hs,_⟩ := all U hU; ⟨s,hs⟩),
    materialized_flatten S Q all,?_⟩
  intro s hs
  obtain ⟨U,hU,hr⟩ := (source_component S Q s).1 hs
  exact ⟨U,hU,hr,component_labels S s U Q hr properS hQ hU,
    restricted_nodup S s U hr properS,leaves_nonempty s⟩

theorem materialized_partition (S : Tree) (Q : List (List Nat))
    (properS : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true) :
    partitionCheck (leaves S) ((sourceForest S Q).map leaves) = true := by
  have he := (checked_materialization S Q properS hQ).2.1
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true] at hQ ⊢
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB
    obtain ⟨s,hs,rfl⟩ := List.mem_map.1 hB
    simpa using leaves_nonempty s
  · intro x hx
    rw [he.count_eq x]
    exact hQ.1.2 x hx
  · intro x hx
    exact hQ.2 x (he.mem_iff.1 hx)

theorem sourceForest_proper (T S : Tree) (Q : List (List Nat))
    (properT : (leaves T).Nodup) (properS : (leaves S).Nodup)
    (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
    (hQ : partitionCheck (leaves S) Q = true) :
    proper (some T) (sourceForest S Q) = true := by
  simp only [proper,labels,Bool.and_eq_true]
  exact ⟨decide_eq_true properT,(partition_labels_congr _ _ _ same).2 (materialized_partition S Q properS hQ)⟩

theorem exact_additional_cost (S : Tree) (Q F : List (List Nat))
    (properS : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true) :
    additionalCost (sourceForest S Q) F = F.length - Q.length := by
  simp only [additionalCost,(checked_materialization S Q properS hQ).1]

theorem contained_members (B U V : List Nat) (same : ∀ x, x ∈ U ↔ x ∈ V) :
    contained B U = contained B V := by
  induction B with
  | nil => rfl
  | cons x B ih =>
    have he : U.contains x = V.contains x := by
      cases hu : U.contains x <;> cases hv : V.contains x <;> simp_all
    simp only [contained,List.all_cons,he]
    exact congrArg (fun b => V.contains x && b) ih

theorem family_members (U V : List Nat) (F : List (List Nat))
    (same : ∀ x, x ∈ U ↔ x ∈ V) : family U F = family V F := by
  apply List.filter_congr
  intro B hB
  exact contained_members B U V same

end OutputState
