import ActualProgram

namespace AllGoodDP
open RMAF RestrictionBridge

theorem minimal_subset_span (t : Tree) (B : List Nat) :
    minimalVertices B t ⊆ rootedSpan B t := by
  induction t with
  | leaf x => exact List.Subset.refl _
  | node l r hl hr =>
    intro v hv
    cases hbl : (rootedSpan B l).isEmpty <;> cases hbr : (rootedSpan B r).isEmpty
    all_goals
      try have el : rootedSpan B l = [] := List.isEmpty_iff.1 hbl
      try have er : rootedSpan B r = [] := List.isEmpty_iff.1 hbr
      try have ml := minimal_nil_of_span_nil B l el
      try have mr := minimal_nil_of_span_nil B r er
      simp_all [minimalVertices,rootedSpan,prependSide,List.subset_def]
    all_goals
      obtain ⟨a,ha,rfl⟩ := hv
      exact Or.inr ⟨a,by first | exact hl ha | exact hr ha,rfl⟩

theorem clear_min_of_root (t : Tree) (A B : List Nat)
    (h : Clear (rootedSpan A t) (minimalVertices B t)) :
    Clear (minimalVertices A t) (minimalVertices B t) := by
  exact fun v hv hb => h v (minimal_subset_span t A hv) hb

theorem selection_congr (t : Tree) (A B : List Nat)
    (h : ∀ x ∈ leaves t, x ∈ A ↔ x ∈ B) :
    rootedSpan A t = rootedSpan B t ∧ minimalVertices A t = minimalVertices B t := by
  induction t with
  | leaf x => have hx := h x (by simp [leaves]); simp [rootedSpan,minimalVertices,hx]
  | node l r hl hr =>
    have il := hl (fun x hx => h x (by simp [leaves,hx]))
    have ir := hr (fun x hx => h x (by simp [leaves,hx]))
    simp [rootedSpan,minimalVertices,il,ir]

theorem no_selection (t : Tree) (A : List Nat) (h : ∀ x ∈ leaves t, x ∉ A) :
    rootedSpan A t = [] ∧ minimalVertices A t = [] := by
  induction t with
  | leaf x => have hx := h x (by simp [leaves]); simp [rootedSpan,minimalVertices,hx]
  | node l r hl hr =>
    have il := hl (fun x hx => h x (by simp [leaves,hx]))
    have ir := hr (fun x hx => h x (by simp [leaves,hx]))
    simp [rootedSpan,minimalVertices,il,ir,prependSide]

theorem split_subset (p : Paint) :
    (split p).1 ⊆ leaves (erase p) ∧ ∀ B ∈ (split p).2, B ⊆ leaves (erase p) := by
  have hm : ∀ B ∈ rawBlocks p, B ⊆ leaves (erase p) := by
    intro B hB x hx
    have hpos : 0 < (rawBlocks p).flatten.count x :=
      List.count_pos_iff.2 (List.mem_flatten.2 ⟨B,hB,hx⟩)
    rw [raw_count] at hpos
    exact List.count_pos_iff.1 hpos
  exact ⟨hm _ (by simp [rawBlocks]),fun B hB => hm B (by simp [rawBlocks,hB])⟩

theorem sibling_disjoint (l r : Tree) (hn : (leaves (.node l r)).Nodup) :
    ∀ x ∈ leaves l, x ∉ leaves r := by
  intro x hl hr
  have hc := List.nodup_iff_count.1 hn x
  have hp := List.count_pos_iff.2 hl
  have hq := List.count_pos_iff.2 hr
  simp only [leaves,List.count_append] at hc
  omega

theorem child_selection_left (l r : Tree) (hn : (leaves (.node l r)).Nodup)
    (A : List Nat) (ha : A ⊆ leaves l) :
    rootedSpan A r = [] ∧ minimalVertices A r = [] := by
  apply no_selection
  intro x hx hxa
  exact sibling_disjoint l r hn x (ha hxa) hx

theorem child_selection_right (l r : Tree) (hn : (leaves (.node l r)).Nodup)
    (A : List Nat) (ha : A ⊆ leaves r) :
    rootedSpan A l = [] ∧ minimalVertices A l = [] := by
  apply no_selection
  intro x hx hxa
  exact sibling_disjoint l r hn x hx (ha hxa)

theorem minimal_left (l r : Tree) (A : List Nat) (he : rootedSpan A r = []) :
    minimalVertices A (.node l r) = prependSide false (minimalVertices A l) := by
  have hm := minimal_nil_of_span_nil A r he
  cases hl : (rootedSpan A l).isEmpty
  · simp [minimalVertices,hl,he]
  · have hnil := minimal_nil_of_span_nil A l (List.isEmpty_iff.1 hl)
    simp [minimalVertices,hl,hm,hnil,prependSide]

theorem minimal_right (l r : Tree) (A : List Nat) (he : rootedSpan A l = []) :
    minimalVertices A (.node l r) = prependSide true (minimalVertices A r) := by
  simp [minimalVertices,he]

theorem active_left_clear (l r : Tree) (A D B : List Nat)
    (har : rootedSpan A r = []) (hdl : rootedSpan D l = [])
    (hbr : rootedSpan B r = [])
    (hclear : Clear (rootedSpan A l) (minimalVertices B l)) :
    Clear (rootedSpan (A ++ D) (.node l r)) (minimalVertices B (.node l r)) := by
  have hal := (selection_congr l (A ++ D) A (by
    intro x hx
    have hd : x ∉ D := by
      intro hxd
      obtain ⟨u,hu⟩ := restriction_exists l D ⟨x,hx,hxd⟩
      have hh := span_empty D l
      simp [hdl,hu] at hh
    simp [hd])).1
  have hdr := (selection_congr r (A ++ D) D (by
    intro x hx
    have ha : x ∉ A := by
      intro hxa
      obtain ⟨u,hu⟩ := restriction_exists r A ⟨x,hx,hxa⟩
      have hh := span_empty A r
      simp [har,hu] at hh
    simp [ha])).1
  rw [minimal_left l r B hbr]
  cases hl : (rootedSpan A l).isEmpty <;> cases hr : (rootedSpan D r).isEmpty <;>
    simp [rootedSpan,hal,hdr,hl,hr,hclear]

theorem active_right_clear (l r : Tree) (A D B : List Nat)
    (har : rootedSpan A r = []) (hdl : rootedSpan D l = [])
    (hbl : rootedSpan B l = [])
    (hclear : Clear (rootedSpan D r) (minimalVertices B r)) :
    Clear (rootedSpan (A ++ D) (.node l r)) (minimalVertices B (.node l r)) := by
  have hal := (selection_congr l (A ++ D) A (by
    intro x hx
    have hd : x ∉ D := by
      intro hxd
      obtain ⟨u,hu⟩ := restriction_exists l D ⟨x,hx,hxd⟩
      have hh := span_empty D l
      simp [hdl,hu] at hh
    simp [hd])).1
  have hdr := (selection_congr r (A ++ D) D (by
    intro x hx
    have ha : x ∉ A := by
      intro hxa
      obtain ⟨u,hu⟩ := restriction_exists r A ⟨x,hx,hxa⟩
      have hh := span_empty A r
      simp [har,hu] at hh
    simp [ha])).1
  rw [minimal_right l r B hbl]
  cases hl : (rootedSpan A l).isEmpty <;> cases hr : (rootedSpan D r).isEmpty <;>
    simp [rootedSpan,hal,hdr,hl,hr,hclear]

theorem pairwise_iff (t : Tree) (F : List (List Nat)) :
    pairwiseEmbeddings t F = true ↔
      F.Pairwise (fun B C => Clear (minimalVertices B t) (minimalVertices C t)) := by
  induction F with
  | nil => simp [pairwiseEmbeddings]
  | cons B F ih => simp [pairwiseEmbeddings,List.all_eq_true,clear_iff,List.pairwise_cons,ih]

theorem pairwise_lift_left (l r : Tree) (F : List (List Nat))
    (he : ∀ B ∈ F, rootedSpan B r = []) (hp : pairwiseEmbeddings l F = true) :
    pairwiseEmbeddings (.node l r) F = true := by
  apply (pairwise_iff _ _).2
  apply List.Pairwise.imp_of_mem (p := (pairwise_iff _ _).1 hp)
  intro B C hB hC hclear
  rw [minimal_left l r B (he B hB),minimal_left l r C (he C hC),clear_prepend_same]
  exact hclear

theorem pairwise_lift_right (l r : Tree) (F : List (List Nat))
    (he : ∀ B ∈ F, rootedSpan B l = []) (hp : pairwiseEmbeddings r F = true) :
    pairwiseEmbeddings (.node l r) F = true := by
  apply (pairwise_iff _ _).2
  apply List.Pairwise.imp_of_mem (p := (pairwise_iff _ _).1 hp)
  intro B C hB hC hclear
  rw [minimal_right l r B (he B hB),minimal_right l r C (he C hC),clear_prepend_same]
  exact hclear

theorem combine_regions (l r : Tree) (A D : List Nat) (F G : List (List Nat))
    (hn : (leaves (.node l r)).Nodup)
    (ha : A ⊆ leaves l) (hd : D ⊆ leaves r)
    (hf : ∀ B ∈ F, B ⊆ leaves l) (hg : ∀ B ∈ G, B ⊆ leaves r)
    (hpf : pairwiseEmbeddings l F = true) (hpg : pairwiseEmbeddings r G = true)
    (hcf : ∀ B ∈ F, Clear (rootedSpan A l) (minimalVertices B l))
    (hcg : ∀ B ∈ G, Clear (rootedSpan D r) (minimalVertices B r)) :
    pairwiseEmbeddings (.node l r) ((A ++ D) :: (F ++ G)) = true ∧
    ∀ B ∈ F ++ G, Clear (rootedSpan (A ++ D) (.node l r))
      (minimalVertices B (.node l r)) := by
  have har := (child_selection_left l r hn A ha).1
  have hdl := (child_selection_right l r hn D hd).1
  have hfr := fun B hB => (child_selection_left l r hn B (hf B hB)).1
  have hgl := fun B hB => (child_selection_right l r hn B (hg B hB)).1
  have hfpar := pairwise_lift_left l r F hfr hpf
  have hgpar := pairwise_lift_right l r G hgl hpg
  have hc : ∀ B ∈ F ++ G, Clear (rootedSpan (A ++ D) (.node l r))
      (minimalVertices B (.node l r)) := by
    intro B hB
    rcases List.mem_append.1 hB with hB | hB
    · exact active_left_clear l r A D B har hdl (hfr B hB) (hcf B hB)
    · exact active_right_clear l r A D B har hdl (hgl B hB) (hcg B hB)
  refine ⟨?_,hc⟩
  apply (pairwise_iff _ _).2
  rw [List.pairwise_cons,List.pairwise_append]
  refine ⟨?_,(pairwise_iff _ _).1 hfpar,(pairwise_iff _ _).1 hgpar,?_⟩
  · intro B hB
    exact clear_min_of_root _ _ _ (hc B hB)
  · intro B hB C hC
    rw [minimal_left l r B (hfr B hB),minimal_right l r C (hgl C hC)]
    exact clear_prepend_other _ _

theorem child_package (p : Paint) (c : Nat)
    (hcert : pairwiseEmbeddings (erase p) (rawBlocks p) = true ∧
      ∀ B ∈ (split p).2, Clear (rootedSpan (split p).1 (erase p))
        (minimalVertices B (erase p))) :
    let A := if c == root p then (split p).1 else []
    let F := if c == root p then (split p).2 else (split p).1 :: (split p).2
    A ⊆ leaves (erase p) ∧ (∀ B ∈ F, B ⊆ leaves (erase p)) ∧
      pairwiseEmbeddings (erase p) F = true ∧
      ∀ B ∈ F, Clear (rootedSpan A (erase p)) (minimalVertices B (erase p)) := by
  have hs := split_subset p
  cases he : c == root p
  · simp only [he,Bool.false_eq_true,ite_false]
    refine ⟨by simp,?_,hcert.1,?_⟩
    · intro B hB
      rcases List.mem_cons.1 hB with rfl | hB
      · exact hs.1
      · exact hs.2 B hB
    · intro B hB
      have hn := (no_selection (erase p) [] (by simp)).1
      simp [hn]
  · simp only [he,ite_true]
    refine ⟨hs.1,hs.2,?_,hcert.2⟩
    have hh := hcert.1
    simp only [rawBlocks,pairwiseEmbeddings,Bool.and_eq_true] at hh
    exact hh.2

theorem split_certificate (p : Paint) (hn : (leaves (erase p)).Nodup) :
    pairwiseEmbeddings (erase p) (rawBlocks p) = true ∧
    ∀ B ∈ (split p).2, Clear (rootedSpan (split p).1 (erase p))
      (minimalVertices B (erase p)) := by
  induction p with
  | leaf x c => simp [rawBlocks,split,erase,pairwiseEmbeddings]
  | node c l r hl hr =>
    have hnl : (leaves (erase l)).Nodup := List.Sublist.nodup (by simp [erase,leaves]) hn
    have hnr : (leaves (erase r)).Nodup := List.Sublist.nodup (by simp [erase,leaves]) hn
    have pl := child_package l c (hl hnl)
    have pr := child_package r c (hr hnr)
    have hh := combine_regions (erase l) (erase r)
      (if c == root l then (split l).1 else [])
      (if c == root r then (split r).1 else [])
      (if c == root l then (split l).2 else (split l).1 :: (split l).2)
      (if c == root r then (split r).2 else (split r).1 :: (split r).2)
      hn pl.1 pr.1 pl.2.1 pr.2.1 pl.2.2.1 pr.2.2.1 pl.2.2.2 pr.2.2.2
    simpa only [erase,rawBlocks,split] using hh

theorem blocks_embeddings (p : Paint) (hn : (leaves (erase p)).Nodup) :
    pairwiseEmbeddings (erase p) (blocks p) = true := by
  apply (pairwise_iff _ _).2
  exact List.Pairwise.filter _ ((pairwise_iff _ _).1 (split_certificate p hn).1)

theorem candidate_embeddings (t : Tree) (ss : List Tree)
    (hp : ForestState.proper (some t) ss = true) :
    pairwiseEmbeddings t (candidate (some t) ss) = true := by
  have hv := (actual_paint_spec t ss hp).1
  have he := valid_erase hv
  have hn := (proper_parts (some t) ss hp).1
  have hc := blocks_embeddings _ (he.symm ▸ hn)
  rw [he] at hc
  exact hc

end AllGoodDP
