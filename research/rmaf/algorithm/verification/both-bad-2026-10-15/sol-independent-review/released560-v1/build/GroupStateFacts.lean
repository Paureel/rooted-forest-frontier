import GroupState

namespace ForestState
open RMAF RestrictionBridge

theorem agrees_parts (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (h : agrees T ss F = true) :
    proper T ss = true ∧ partitionCheck (labels T) F = true ∧
    (∀ B ∈ F, ∃ s ∈ ss, B ⊆ leaves s) ∧
    targetEmbeddings T F = true ∧ (∀ s ∈ ss, sourceCheck T F s = true) := by
  simpa only [agrees,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,contained_iff,
    and_assoc] using h

theorem proper_parts (T : Option Tree) (ss : List Tree) (h : proper T ss = true) :
    (labels T).Nodup ∧ partitionCheck (labels T) (ss.map leaves) = true := by
  simpa [proper] using h

theorem tree_of_singleton_leaves (s : Tree) (a : Nat) (h : leaves s = [a]) : s = .leaf a := by
  cases s with
  | leaf x => simpa [leaves] using h
  | node l r =>
    have hl := List.length_pos_iff.2 (leaves_nonempty l)
    have hr := List.length_pos_iff.2 (leaves_nonempty r)
    have he := congrArg List.length h
    simp only [leaves,List.length_append,List.length_cons,List.length_nil] at he
    omega

theorem checked_flatten_nodup (L : List Nat) (F : List (List Nat))
    (h : partitionCheck L F = true) : F.flatten.Nodup := by
  apply List.nodup_iff_count.2
  intro x
  by_cases hx : x ∈ L
  · rw [checked_count L F h hx]
    omega
  · have hn : x ∉ F.flatten := by
      intro hm
      obtain ⟨B,hB,hxB⟩ := List.mem_flatten.1 hm
      exact hx (checked_label L F h hB hxB)
    rw [List.count_eq_zero.2 hn]
    omega

theorem subset_singleton_eq (B : List Nat) (a : Nat) (hn : B ≠ [])
    (sub : B ⊆ [a]) (nd : B.Nodup) : B = [a] := by
  cases B with
  | nil => contradiction
  | cons x xs =>
    have hx : x = a := by simpa using sub (by simp)
    subst x
    have hxs : xs = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro y hy
      have he : y = a := by simpa using sub (by simp [hy])
      subst y
      exact (List.nodup_cons.1 nd).1 hy
    simp [hxs]

theorem checked_block_nodup (L : List Nat) (F : List (List Nat))
    (h : partitionCheck L F = true) (B : List Nat) (hB : B ∈ F) : B.Nodup := by
  apply List.nodup_iff_count.2
  intro x
  have hle : B.count x ≤ F.flatten.count x := by
    clear h
    induction F with
    | nil => simp at hB
    | cons C F ih =>
      rcases List.mem_cons.1 hB with he | hm
      · subst C
        simp only [List.flatten_cons,List.count_append]
        omega
      · have hh := ih hm
        simp only [List.flatten_cons,List.count_append]
        omega
  have hc := List.nodup_iff_count.1 (checked_flatten_nodup L F h) x
  omega

theorem singleton_source_owner (T : Option Tree) (ss : List Tree) (a : Nat)
    (hp : proper T ss = true) (ha : .leaf a ∈ ss) :
    a ∈ labels T ∧ ∀ s ∈ ss, a ∈ leaves s → s = .leaf a := by
  have hQ := (proper_parts T ss hp).2
  have hleaf : [a] ∈ ss.map leaves := List.mem_map.2 ⟨.leaf a,ha,rfl⟩
  have hal : a ∈ labels T := checked_label (labels T) (ss.map leaves) hQ hleaf (by simp)
  obtain ⟨U,hU,hxU,hcU,unique⟩ := unique_label_owner (ss.map leaves) a
    (checked_count (labels T) (ss.map leaves) hQ hal)
  have he := unique [a] hleaf (by simp)
  refine ⟨hal,?_⟩
  intro s hs has
  have hsu := unique (leaves s) (List.mem_map.2 ⟨s,hs,rfl⟩) has
  exact tree_of_singleton_leaves s a (hsu.trans he.symm)

theorem singleton_forced (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (a : Nat) (h : agrees T ss F = true) (ha : .leaf a ∈ ss) :
    [a] ∈ F ∧ F.count [a] = 1 ∧ ∀ B ∈ F, a ∈ B → B = [a] := by
  obtain ⟨hp,hF,href,ht,hs⟩ := agrees_parts T ss F h
  obtain ⟨hal,owner⟩ := singleton_source_owner T ss a hp ha
  have force : ∀ B ∈ F, a ∈ B → B = [a] := by
    intro B hB haB
    obtain ⟨s,hs,hBs⟩ := href B hB
    have he := owner s hs (hBs haB)
    rw [he] at hBs
    apply subset_singleton_eq B a (checked_nonempty (labels T) F hF B hB) hBs
    exact checked_block_nodup (labels T) F hF B hB
  obtain ⟨B,hB,haB⟩ := checked_covers (labels T) F hF hal
  have hb := force B hB haB
  have hsingle : [a] ∈ F := by simpa [hb] using hB
  obtain ⟨U,hU,hxU,hcU,unique⟩ := unique_label_owner F a
    (checked_count (labels T) F hF hal)
  have he := unique [a] hsingle (by simp)
  exact ⟨hsingle,by simpa [←he] using hcU,force⟩

theorem singleton_additional_cost (T : Option Tree) (ss : List Tree)
    (F : List (List Nat)) (a : Nat) (h : agrees T ss F = true)
    (ha : .leaf a ∈ ss) :
    additionalCost (cleanupSources ss a) (cleanupForest F a) = additionalCost ss F := by
  have hf := (singleton_forced T ss F a h ha).1
  have hfl := List.length_pos_iff.2 (List.ne_nil_of_mem hf)
  have hsl := List.length_pos_iff.2 (List.ne_nil_of_mem ha)
  simp only [additionalCost,cleanupSources,cleanupForest,List.length_erase_of_mem hf,
    List.length_erase_of_mem ha]
  omega

end ForestState

namespace ForestState
open RMAF RestrictionBridge

theorem initial_state_agreement_iff (t s : Tree) (F : List (List Nat))
    (hp : proper (some t) [s] = true) :
    agrees (some t) [s] F = true ↔ agreement t s F = true := by
  constructor
  · intro h
    obtain ⟨hproper,hF,href,ht,hs⟩ := agrees_parts (some t) [s] F h
    have sub : ∀ B ∈ F, B ⊆ leaves s := by
      intro B hB
      obtain ⟨u,hu,hBu⟩ := href B hB
      have he : u = s := by simpa using hu
      simpa [he] using hBu
    have hf : family (leaves s) F = F := by
      apply List.filter_eq_self.2
      intro B hB
      exact (contained_iff B (leaves s)).2 (sub B hB)
    have hs0 := hs s (by simp)
    have htarget : targetAgrees (some t) s = restrictionAgrees t s := by funext B; rfl
    have hsc : partitionCheck (leaves s) F = true ∧
        F.all (restrictionAgrees t s) = true ∧ pairwiseEmbeddings s F = true := by
      simpa only [sourceCheck,hf,htarget,Bool.and_eq_true,and_assoc] using hs0
    simp only [agreement,Bool.and_eq_true]
    exact ⟨⟨⟨⟨hF,hsc.1⟩,hsc.2.1⟩,ht⟩,hsc.2.2⟩
  · intro h
    have ho : partitionCheck (leaves t) F = true ∧ partitionCheck (leaves s) F = true ∧
        F.all (restrictionAgrees t s) = true ∧ pairwiseEmbeddings t F = true ∧
        pairwiseEmbeddings s F = true := by
      simpa only [agreement,Bool.and_eq_true,and_assoc] using h
    have sub : ∀ B ∈ F, B ⊆ leaves s := by
      intro B hB x hx
      exact checked_label (leaves s) F ho.2.1 hB hx
    have hf : family (leaves s) F = F := by
      apply List.filter_eq_self.2
      intro B hB
      exact (contained_iff B (leaves s)).2 (sub B hB)
    simp only [agrees,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,contained_iff]
    refine ⟨⟨⟨⟨hp,ho.1⟩,?_⟩,ho.2.2.2.1⟩,?_⟩
    · intro B hB; exact ⟨s,by simp,sub B hB⟩
    · intro u hu
      have he : u = s := by simpa using hu
      subst u
      simp only [sourceCheck,hf,targetAgrees,Bool.and_eq_true]
      exact ⟨⟨ho.2.1,ho.2.2.1⟩,ho.2.2.2.2⟩

end ForestState
