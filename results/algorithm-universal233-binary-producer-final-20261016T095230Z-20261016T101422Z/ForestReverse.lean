import ForestOverlap
namespace GenericForest
open RMAF RestrictionBridge ForestState OutputState ForestGroups

theorem proper_sources_nodup (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true) : ss.Nodup := by
  exact List.Pairwise.of_map leaves (fun a b h he => h (congrArg leaves he))
    (checked_family_nodup _ _ (proper_parts _ _ hp).2)

theorem source_family_part (t : Tree) (ss : List Tree) (F : Forest)
    (hp : proper (some t) ss = true) (hF : partitionCheck (leaves t) F = true)
    (own : ∀ B ∈ F, ∃ s ∈ ss, B ⊆ leaves s) (s : Tree) (hs : s ∈ ss) :
    partitionCheck (leaves s) (family (leaves s) F) = true := by
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB
    simpa using checked_nonempty _ _ hF B ((mem_family _ _ _).1 hB).1
  · intro x hx
    have owners : ∀ B ∈ F, x ∈ B → B ⊆ leaves s := by
      intro B hB hxB
      obtain ⟨u,hu,hBu⟩ := own B hB
      have he := source_owner t ss hp u s hu hs x (hBu hxB) hx
      simpa [he] using hBu
    apply beq_iff_eq.2
    rw [count_family_flatten F (leaves s) x owners,
      checked_count _ _ hF ((proper_source_labels t ss hp s hs).2 hx)]
  · intro x hx
    obtain ⟨B,hB,hxB⟩ := List.mem_flatten.1 hx
    exact List.contains_iff_mem.2 (((mem_family _ _ _).1 hB).2 hxB)

theorem source_check_reverse (t s : Tree) (Q F : Forest)
    (hsn : (leaves s).Nodup) (hQ : partitionCheck (leaves s) Q = true)
    (sourceQ : pairwiseEmbeddings s Q = true)
    (hG : partitionCheck (leaves s) (family (leaves s) F) = true)
    (href : RestrictionBridge.Refines (family (leaves s) F) Q)
    (hc : ∀ u ∈ sourceForest s Q, sourceCheck (some t) F u = true) :
    sourceCheck (some t) F s = true := by
  have localClear (U : List Nat) (hU : U ∈ Q) :
      pairwiseEmbeddings s (family U F) = true := by
    obtain ⟨u,hu,hl⟩ := checked_restrictions s Q hsn hQ U hU
    have hcu := hc u ((source_component s Q u).2 ⟨U,hU,hu⟩)
    simp only [sourceCheck,Bool.and_eq_true] at hcu
    have he : family (leaves u) F = family U F := family_members _ _ F (fun _ => hl.mem_iff)
    rw [he] at hcu
    exact (pairwise_transport s u U _ hu (fun B hB => ((mem_family _ _ _).1 hB).2)).2 hcu.2
  simp only [sourceCheck,Bool.and_eq_true]
  refine ⟨⟨hG,?_⟩,?_⟩
  · apply List.all_eq_true.2
    intro B hB
    obtain ⟨U,hU,hBU⟩ := href B hB
    obtain ⟨u,hu,hl⟩ := checked_restrictions s Q hsn hQ U hU
    have hcu := hc u ((source_component s Q u).2 ⟨U,hU,hu⟩)
    simp only [sourceCheck,Bool.and_eq_true] at hcu
    have hBF := ((mem_family _ _ _).1 hB).1
    have hBu : B ⊆ leaves u := fun _ hx => hl.mem_iff.2 (hBU hx)
    change restrictionAgrees t s B = true
    rw [←source_topology t s u U B hu hBU]
    exact List.all_eq_true.1 hcu.1.2 B ((mem_family _ _ _).2 ⟨hBF,hBu⟩)
  · apply (pairwise_iff s _).2
    apply List.Pairwise.imp_of_mem (R := fun B C => B ≠ C)
      (p := checked_family_nodup _ _ hG)
    intro B C hB hC hne
    obtain ⟨U,hU,hBU⟩ := href B hB
    obtain ⟨V,hV,hCV⟩ := href C hC
    by_cases he : U = V
    · subst V
      exact pairwise_distinct s (family U F) (localClear U hU) B C
        ((mem_family _ _ _).2 ⟨((mem_family _ _ _).1 hB).1,hBU⟩)
        ((mem_family _ _ _).2 ⟨((mem_family _ _ _).1 hC).1,hCV⟩) hne
    · exact cross_subblocks s Q sourceQ U V B C hU hV he hBU hCV

theorem replacement_reverse (t : Tree) (pre : List Tree) (s : Tree) (post : List Tree)
    (Q F : Forest) (hp : proper (some t) (pre ++ [s] ++ post) = true)
    (hQ : partitionCheck (leaves s) Q = true) (sourceQ : pairwiseEmbeddings s Q = true)
    (ha : agrees (some t) (replaced pre s post Q) F = true) :
    agrees (some t) (pre ++ [s] ++ post) F = true ∧
      RestrictionBridge.Refines (family (leaves s) F) Q := by
  obtain ⟨hpnew,hF,hown,hE,hS⟩ := agrees_parts _ _ _ ha
  have hs : s ∈ pre ++ [s] ++ post := by simp
  have hsn := (proper_source_labels t _ hp s hs).1
  have hnd := proper_sources_nodup t _ hp
  have hnd' : (pre ++ (s :: post)).Nodup := by simpa [List.append_assoc] using hnd
  have ns : s ∉ pre ∧ s ∉ post := by
    have hh := List.nodup_append.1 hnd'
    exact ⟨fun h => hh.2.2 s h s (by simp) rfl,(List.nodup_cons.1 hh.2.1).1⟩
  have oldOwn : ∀ B ∈ F, ∃ r ∈ pre ++ [s] ++ post, B ⊆ leaves r := by
    intro B hB
    obtain ⟨r,hr,hBr⟩ := hown B hB
    simp only [replaced,List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact ⟨r,by simp [hr],hBr⟩
    · obtain ⟨U,hU,hu⟩ := (source_component s Q r).1 hr
      have hl := component_labels s r U Q hu hsn hQ hU
      exact ⟨s,hs,fun _ hx => checked_label _ _ hQ hU (hl.mem_iff.1 (hBr hx))⟩
    · exact ⟨r,by simp [hr],hBr⟩
  have href : RestrictionBridge.Refines (family (leaves s) F) Q := by
    intro B hB
    have bb := (mem_family _ _ _).1 hB
    obtain ⟨r,hr,hBr⟩ := hown B bb.1
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B (checked_nonempty _ _ hF B bb.1)
    simp only [replaced,List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · have he := source_owner t _ hp r s (by simp [hr]) hs x (hBr hx) (bb.2 hx)
      exact False.elim (ns.1 (he ▸ hr))
    · obtain ⟨U,hU,hu⟩ := (source_component s Q r).1 hr
      have hl := component_labels s r U Q hu hsn hQ hU
      exact ⟨U,hU,fun _ hx => hl.mem_iff.1 (hBr hx)⟩
    · have he := source_owner t _ hp r s (by simp [hr]) hs x (hBr hx) (bb.2 hx)
      exact False.elim (ns.2 (he ▸ hr))
  refine ⟨?_,href⟩
  simp only [agrees,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,contained_iff]
  refine ⟨⟨⟨⟨hp,hF⟩,oldOwn⟩,hE⟩,?_⟩
  intro r hr
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with (hr | rfl) | hr
  · exact hS r (by simp [replaced,hr])
  · exact source_check_reverse t r Q F hsn hQ sourceQ
      (source_family_part t _ F hp hF oldOwn r hs) href
      (fun u hu => hS u (by simp [replaced,hu]))
  · exact hS r (by simp [replaced,hr])

end GenericForest
