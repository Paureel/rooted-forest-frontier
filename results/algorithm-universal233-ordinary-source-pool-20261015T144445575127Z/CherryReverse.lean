import CherryLeafClear

namespace ForestState
open RMAF RestrictionBridge

theorem partition_add_singleton (L : List Nat) (G : List (List Nat)) (a : Nat)
    (nd : L.Nodup) (ha : a ∈ L) (hp : partitionCheck (L.erase a) G = true) :
    partitionCheck L ([a] :: G) = true := by
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB
    rcases List.mem_cons.1 hB with he | hm
    · subst B; simp
    · have hn := checked_nonempty (L.erase a) G hp B hm
      simpa using hn
  · intro x hx
    apply beq_iff_eq.2
    by_cases he : x = a
    · subst x
      have hz : G.flatten.count a = 0 := by
        apply List.count_eq_zero.2
        intro hm
        obtain ⟨B,hB,haB⟩ := List.mem_flatten.1 hm
        exact nd.not_mem_erase (checked_label (L.erase a) G hp hB haB)
      simp [hz]
    · have hc := checked_count (L.erase a) G hp ((List.mem_erase_of_ne he).2 hx)
      simp [List.count_append,Ne.symm he,hc]
  · intro x hx
    apply List.contains_iff_mem.2
    rcases List.mem_flatten.1 hx with ⟨B,hB,hxB⟩
    rcases List.mem_cons.1 hB with he | hm
    · subst B
      have he : x = a := by simpa using hxB
      simpa [he] using ha
    · exact List.mem_of_mem_erase (checked_label (L.erase a) G hp hm hxB)

theorem proper_singleton_restriction (t : Tree) (a : Nat) (nd : (leaves t).Nodup)
    (ha : a ∈ leaves t) : restrict [a] t = some (.leaf a) := by
  obtain ⟨u,hu⟩ := restriction_exists t [a] ⟨a,ha,by simp⟩
  have sub : leaves u ⊆ [a] := by
    intro x hx
    exact ((restricted_labels_exact t u [a] hu).1 hx).2
  have heu := subset_singleton_eq (leaves u) a (leaves_nonempty u) sub
    (restricted_nodup t u [a] hu nd)
  have he := tree_of_singleton_leaves u a heu
  simpa [he] using hu

theorem family_add_absent (U : List Nat) (G : List (List Nat)) (a : Nat) (hn : a ∉ U) :
    family U ([a] :: G) = family U G := by
  have hp : contained [a] U = false := by simp [contained,hn]
  simp [family,hp]

theorem family_singleton_reconstruction (T : Option Tree) (G : List (List Nat)) (a : Nat)
    (nd : (labels T).Nodup) (hG : partitionCheck (labels (cleanupTarget T a)) G = true) :
    family [a] ([a] :: G) = [[a]] := by
  have hn : ∀ B ∈ G, ¬B ⊆ [a] := by
    intro B hB hs
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B
      (checked_nonempty (labels (cleanupTarget T a)) G hG B hB)
    have he : x = a := by simpa using hs hx
    have hm := checked_label (labels (cleanupTarget T a)) G hG hB hx
    rw [cleanup_labels T a nd,he] at hm
    exact nd.not_mem_erase hm
  have he : family [a] G = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro B hB
    obtain ⟨hBG,sub⟩ := (mem_family B [a] G).1 hB
    exact hn B hBG sub
  simp [family] at he ⊢
  exact he

theorem singleton_cleanup_reverse (T : Option Tree) (ss : List Tree) (G : List (List Nat))
    (a : Nat) (hp : proper T ss = true) (ha : .leaf a ∈ ss)
    (h : agrees (cleanupTarget T a) (cleanupSources ss a) G = true) :
    agrees T ss ([a] :: G) = true := by
  obtain ⟨hpr,hG,href,ht,hs⟩ := agrees_parts _ _ _ h
  have nd := (proper_parts T ss hp).1
  have hal := (singleton_source_owner T ss a hp ha).1
  have homit := remaining_sources_omit T ss a hp ha
  have hGl : partitionCheck ((labels T).erase a) G = true := by
    simpa only [cleanup_labels T a nd] using hG
  have hsub : ∀ B ∈ G, B ⊆ (labels T).erase a := by
    intro B hB x hx
    exact checked_label _ _ hGl hB hx
  have hGa : ∀ B ∈ G, a ∉ B := by
    intro B hB hm
    exact nd.not_mem_erase (hsub B hB hm)
  simp only [agrees,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,contained_iff]
  refine ⟨⟨⟨⟨hp,partition_add_singleton (labels T) G a nd hal hGl⟩,?_⟩,?_⟩,?_⟩
  · intro B hB
    rcases List.mem_cons.1 hB with he | hm
    · subst B; exact ⟨.leaf a,ha,by simp [leaves]⟩
    · obtain ⟨s,hs,hBs⟩ := href B hm
      exact ⟨s,List.mem_of_mem_erase hs,hBs⟩
  · cases T with
    | none => simp [labels] at hal
    | some t =>
      have htG : pairwiseEmbeddings t G = true := by
        cases hr : restrict ((leaves t).erase a) t with
        | none =>
          have hz : labels (cleanupTarget (some t) a) = [] := by simp [cleanupTarget,labels,hr]
          rw [hz] at hG
          have he := partition_empty G hG
          simp [he,pairwiseEmbeddings]
        | some u =>
          have hu : pairwiseEmbeddings u G = true := by
            simpa [cleanupTarget,labels,hr,targetEmbeddings] using ht
          exact (pairwise_transport t u ((leaves t).erase a) G hr hsub).2 hu
      change pairwiseEmbeddings t ([a] :: G) = true
      simp only [pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true]
      refine ⟨?_,htG⟩
      intro B hB
      exact (clear_iff _ _).2 (singleton_clear t a B nd (hGa B hB)).2
  · intro s hss
    by_cases he : s = .leaf a
    · subst s
      simp only [sourceCheck,leaves]
      rw [family_singleton_reconstruction T G a nd hG]
      cases T with
      | none => simp [labels] at hal
      | some t =>
        have hr := proper_singleton_restriction t a nd hal
        simp [partitionCheck,pairwiseEmbeddings,targetAgrees,restrictionAgrees,restrict,hr,sameShape]
    · have hsr : s ∈ cleanupSources ss a := (List.mem_erase_of_ne he).2 hss
      have hsold := hs s hsr
      have hf := family_add_absent (leaves s) G a (homit s hsr)
      simp only [sourceCheck] at hsold ⊢
      rw [hf]
      have ho : partitionCheck (leaves s) (family (leaves s) G) = true ∧
          (family (leaves s) G).all (targetAgrees (cleanupTarget T a) s) = true ∧
          pairwiseEmbeddings s (family (leaves s) G) = true := by
        simpa only [Bool.and_eq_true,and_assoc] using hsold
      simp only [Bool.and_eq_true,and_assoc]
      refine ⟨ho.1,?_,ho.2.2⟩
      apply List.all_eq_true.2
      intro B hB
      have hBG := (mem_family B (leaves s) G).1 hB |>.1
      rw [←target_agrees_cleanup T a s B (hsub B hBG)]
      exact List.all_eq_true.1 ho.2.1 B hB

theorem singleton_reconstruction_cost (ss : List Tree) (G : List (List Nat)) (a : Nat)
    (ha : .leaf a ∈ ss) :
    additionalCost ss ([a] :: G) = additionalCost (cleanupSources ss a) G := by
  have hsl := List.length_pos_iff.2 (List.ne_nil_of_mem ha)
  simp only [additionalCost,cleanupSources,List.length_cons,List.length_erase_of_mem ha]
  omega

def feasible (T : Option Tree) (ss : List Tree) (q : Nat) : Prop :=
  ∃ F, agrees T ss F = true ∧ additionalCost ss F ≤ q

theorem singleton_decision_equivalence (T : Option Tree) (ss : List Tree) (a q : Nat)
    (hp : proper T ss = true) (ha : .leaf a ∈ ss) :
    feasible T ss q ↔ feasible (cleanupTarget T a) (cleanupSources ss a) q := by
  constructor
  · rintro ⟨F,hF,hcost⟩
    exact ⟨cleanupForest F a,singleton_cleanup_forward T ss F a hF ha,
      by simpa only [singleton_additional_cost T ss F a hF ha] using hcost⟩
  · rintro ⟨G,hG,hcost⟩
    exact ⟨[a] :: G,singleton_cleanup_reverse T ss G a hp ha hG,
      by simpa only [singleton_reconstruction_cost ss G a ha] using hcost⟩

end ForestState
