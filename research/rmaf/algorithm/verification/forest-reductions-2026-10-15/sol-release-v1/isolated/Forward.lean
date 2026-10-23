import Removal

namespace ForestState
open RMAF RestrictionBridge

theorem partition_empty (F : List (List Nat)) (h : partitionCheck [] F = true) : F = [] := by
  cases F with
  | nil => rfl
  | cons B F =>
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B
      (checked_nonempty [] (B :: F) h B (by simp))
    have hm := checked_label [] (B :: F) h (by simp) hx
    simp at hm

theorem pairwise_erase (t : Tree) (F : List (List Nat)) (B : List Nat)
    (h : pairwiseEmbeddings t F = true) : pairwiseEmbeddings t (F.erase B) = true := by
  induction F with
  | nil => simp [pairwiseEmbeddings]
  | cons C F ih =>
    have hh : (∀ D ∈ F, disjointVertices (minimalVertices C t) (minimalVertices D t) = true) ∧
        pairwiseEmbeddings t F = true := by simpa [pairwiseEmbeddings,List.all_eq_true] using h
    by_cases he : C = B
    · subst C; simpa using hh.2
    · have her : (C :: F).erase B = C :: F.erase B :=
        List.erase_cons_tail (by simpa only [beq_iff_eq] using he)
      rw [her]
      simp only [pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true]
      exact ⟨fun D hD => hh.1 D (List.mem_of_mem_erase hD),ih hh.2⟩

theorem family_erase_absent (U : List Nat) (F : List (List Nat)) (a : Nat) (hn : a ∉ U) :
    family U (F.erase [a]) = family U F := by
  induction F with
  | nil => rfl
  | cons B F ih =>
    by_cases he : B = [a]
    · subst B
      have hp : contained [a] U = false := by simp [contained,hn]
      simp [family,hp]
    · have her : (B :: F).erase [a] = B :: F.erase [a] :=
        List.erase_cons_tail (by simpa only [beq_iff_eq] using he)
      rw [her]
      cases hp : contained B U <;> simp_all [family]

theorem remaining_sources_omit (T : Option Tree) (ss : List Tree) (a : Nat)
    (hp : proper T ss = true) (ha : .leaf a ∈ ss) :
    ∀ s ∈ cleanupSources ss a, a ∉ leaves s := by
  have hc := (proper_parts T ss hp).2
  have hal := (singleton_source_owner T ss a hp ha).1
  have hm : [a] ∈ ss.map leaves := List.mem_map.2 ⟨.leaf a,ha,rfl⟩
  have he := flatten_count_erase (ss.map leaves) [a] hm a
  have ho := checked_count (labels T) (ss.map leaves) hc hal
  rw [←map_cleanup_sources] at he
  intro s hs has
  have hx : a ∈ ((cleanupSources ss a).map leaves).flatten :=
    List.mem_flatten.2 ⟨leaves s,List.mem_map.2 ⟨s,hs,rfl⟩,has⟩
  have hpos := List.count_pos_iff.2 hx
  simp at he
  omega

theorem remaining_forest_sub (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (a : Nat) (h : agrees T ss F = true) (ha : .leaf a ∈ ss) :
    ∀ B ∈ cleanupForest F a, B ⊆ (labels T).erase a := by
  have hparts := agrees_parts T ss F h
  have hp := partition_remove_singleton (labels T) F a hparts.2.1
    (proper_parts T ss hparts.1).1 (singleton_forced T ss F a h ha).1
  intro B hB x hx
  exact checked_label ((labels T).erase a) (cleanupForest F a) hp hB hx

theorem target_agrees_cleanup (T : Option Tree) (a : Nat) (s : Tree) (B : List Nat)
    (hB : B ⊆ (labels T).erase a) :
    targetAgrees (cleanupTarget T a) s B = targetAgrees T s B := by
  cases T with
  | none => rfl
  | some t =>
    cases hr : restrict ((leaves t).erase a) t with
    | none =>
      have hb : restrict B t = none := by
        have hh := restrict_nested t ((leaves t).erase a) B hB
        simpa [hr] using hh.symm
      simp [cleanupTarget,labels,targetAgrees,hr,restrictionAgrees,hb]
    | some u =>
      simp only [cleanupTarget,labels,Option.bind_some,hr,targetAgrees,restrictionAgrees,
        restrict_inside t u ((leaves t).erase a) B hr hB]

theorem singleton_cleanup_forward (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (a : Nat) (h : agrees T ss F = true) (ha : .leaf a ∈ ss) :
    agrees (cleanupTarget T a) (cleanupSources ss a) (cleanupForest F a) = true := by
  obtain ⟨hp,hF,href,ht,hs⟩ := agrees_parts T ss F h
  have nd := (proper_parts T ss hp).1
  have hsingle := (singleton_forced T ss F a h ha).1
  have hsub := remaining_forest_sub T ss F a h ha
  have homit := remaining_sources_omit T ss a hp ha
  have hnewF : partitionCheck (labels (cleanupTarget T a)) (cleanupForest F a) = true := by
    rw [cleanup_labels T a nd]
    exact partition_remove_singleton (labels T) F a hF nd hsingle
  simp only [agrees,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,contained_iff]
  refine ⟨⟨⟨⟨cleanup_proper T ss a hp ha,hnewF⟩,?_⟩,?_⟩,?_⟩
  · intro B hB
    obtain ⟨s,hs,hBs⟩ := href B (List.mem_of_mem_erase hB)
    have hne : s ≠ .leaf a := by
      intro he
      rw [he] at hBs
      obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B
        (checked_nonempty (labels (cleanupTarget T a)) (cleanupForest F a) hnewF B hB)
      have hxa : x = a := by simpa [leaves] using hBs hx
      have hxU := hsub B hB hx
      rw [hxa] at hxU
      exact nd.not_mem_erase hxU
    exact ⟨s,(List.mem_erase_of_ne hne).2 hs,hBs⟩
  · cases T with
    | none =>
      have he : F = [] := partition_empty F hF
      simp [cleanupTarget,cleanupForest,targetEmbeddings,he]
    | some t =>
      cases hr : restrict ((leaves t).erase a) t with
      | none =>
        have hz : labels (cleanupTarget (some t) a) = [] := by simp [cleanupTarget,hr,labels]
        rw [hz] at hnewF
        have he := partition_empty _ hnewF
        simp [cleanupTarget,labels,hr,targetEmbeddings,he]
      | some u =>
        have ht0 : pairwiseEmbeddings t F = true := ht
        have ht1 := pairwise_erase t F [a] ht0
        have ht2 := (pairwise_transport t u ((leaves t).erase a) (cleanupForest F a) hr hsub).1 ht1
        simpa [cleanupTarget,labels,hr,targetEmbeddings] using ht2
  · intro s hsnew
    have hsold := hs s (List.mem_of_mem_erase hsnew)
    have hfamily := family_erase_absent (leaves s) F a (homit s hsnew)
    simp only [sourceCheck] at hsold ⊢
    simp only [Bool.and_eq_true,and_assoc]
    change partitionCheck (leaves s) (family (leaves s) (cleanupForest F a)) = true ∧
      (family (leaves s) (cleanupForest F a)).all (targetAgrees (cleanupTarget T a) s) = true ∧
      pairwiseEmbeddings s (family (leaves s) (cleanupForest F a)) = true
    change family (leaves s) (cleanupForest F a) = family (leaves s) F at hfamily
    rw [hfamily]
    have ho : partitionCheck (leaves s) (family (leaves s) F) = true ∧
        (family (leaves s) F).all (targetAgrees T s) = true ∧
        pairwiseEmbeddings s (family (leaves s) F) = true := by
      simpa only [Bool.and_eq_true,and_assoc] using hsold
    refine ⟨ho.1,?_,ho.2.2⟩
    apply List.all_eq_true.2
    intro B hB
    have hBF := (mem_family B (leaves s) F).1 hB |>.1
    have hBa : a ∉ B := fun hm => homit s hsnew ((mem_family B (leaves s) F).1 hB |>.2 hm)
    have hne : B ≠ [a] := by intro he; simp [he] at hBa
    have hBr : B ∈ cleanupForest F a := (List.mem_erase_of_ne hne).2 hBF
    rw [target_agrees_cleanup T a s B (hsub B hBr)]
    exact List.all_eq_true.1 ho.2.1 B hB

end ForestState
