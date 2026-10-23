import ForestConditional
namespace GenericForest
open RMAF RestrictionBridge ForestState OutputState ForestGroups
open Universal233 Universal233.CoreProgram Universal233.PaidQueries

theorem component_pair_proper (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (s : Tree) (hs : s ∈ ss) :
    ∃ u, componentPair t s = some (u,s) ∧ restrict (leaves s) t = some u ∧
      (leaves u).Perm (leaves s) ∧ DepthOne.proper u s = true := by
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil (leaves s) (RestrictionBridge.leaves_nonempty s)
  obtain ⟨u,hu⟩ := restriction_exists t (leaves s)
    ⟨x,(proper_source_labels t ss hp s hs).2 hx,hx⟩
  have ht : (leaves t).Nodup := (proper_parts _ _ hp).1
  have hm : leaves s ∈ ss.map leaves := List.mem_map.2 ⟨s,hs,rfl⟩
  have hl := component_labels t u (leaves s) (ss.map leaves) hu ht (proper_parts _ _ hp).2 hm
  have hsn := (proper_source_labels t ss hp s hs).1
  refine ⟨u,by simp [componentPair,hu],hu,hl,?_⟩
  simp [DepthOne.proper,restricted_nodup t u _ hu ht,hsn,hl]

theorem multiple_sources_smaller (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (hmultiple : 2 ≤ ss.length) (s : Tree) (hs : s ∈ ss) : (leaves s).length < (leaves t).length := by
  have hlen := List.length_erase_of_mem hs
  have hne : ss.erase s ≠ [] := by intro he; rw [he] at hlen; simp at hlen; omega
  obtain ⟨r,hr⟩ := List.exists_mem_of_ne_nil (ss.erase s) hne
  have hrs : r ∈ ss := List.mem_of_mem_erase hr
  have hsr : s ≠ r := by
    intro he
    exact (proper_sources_nodup t ss hp).not_mem_erase (he ▸ hr)
  obtain ⟨x,hxr⟩ := List.exists_mem_of_ne_nil (leaves r) (RestrictionBridge.leaves_nonempty r)
  have hxs : x ∉ leaves s := fun hx => source_labels_disjoint t ss hp s r hs hrs hsr x hx hxr
  have hsupp := proper_source_labels t ss hp s hs
  have hxT := (proper_source_labels t ss hp r hrs).2 hxr
  have hn : (x :: leaves s).Nodup := List.nodup_cons.2 ⟨hxs,hsupp.1⟩
  have hl := hn.length_le_of_subset (show x :: leaves s ⊆ leaves t from by
    intro y hy; rcases List.mem_cons.1 hy with rfl | hy
    · exact hxT
    · exact hsupp.2 hy)
  simp only [List.length_cons] at hl
  omega

theorem jobs_actual (t : Tree) (ss : List Tree) (js : List (Job (Tree × Tree) Forest))
    (hj : jobs t ss = some js) : ∀ j ∈ js, ∃ s ∈ ss, componentPair t s = some j.problem := by
  induction ss generalizing js with
  | nil => have he : js = [] := by simpa [jobs] using hj.symm
           simp [he]
  | cons s ss ih =>
    cases hp : componentPair t s with
    | none => simp [jobs,hp] at hj
    | some p =>
      have step (j : Job (Tree × Tree) Forest) (he : j.problem = p)
          (hh : (jobs t ss).map (j :: ·) = some js) :
          ∀ k ∈ js, ∃ r ∈ s :: ss, componentPair t r = some k.problem := by
        obtain ⟨tail,ht,hcons⟩ := Option.map_eq_some_iff.1 hh
        subst js
        intro k hk
        rcases List.mem_cons.1 hk with rfl | hk
        · exact ⟨s,by simp,by simpa [he] using hp⟩
        · obtain ⟨r,hr,hp⟩ := ih tail ht k hk
          exact ⟨r,by simp [hr],hp⟩
      cases hc : DepthOne.pretest01 p.1 p.2 with
      | refused => simp [jobs,hp,hc] at hj
      | rejected => exact step (.hard p) rfl (by simpa [jobs,hp,hc] using hj)
      | found c =>
        exact step (.resolved p (DepthOne.cutCost c) (DepthOne.forest s c)) rfl
          (by simpa [jobs,hp,hc] using hj)

theorem jobs_proper_and_smaller (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (hmultiple : 2 ≤ ss.length) (js : List (Job (Tree × Tree) Forest)) (hj : jobs t ss = some js)
    (j : Job (Tree × Tree) Forest) (hjj : j ∈ js) :
    DepthOne.proper j.problem.1 j.problem.2 = true ∧
      (leaves j.problem.1).length < (leaves t).length ∧
      (leaves j.problem.2).length < (leaves t).length := by
  obtain ⟨s,hs,hps⟩ := jobs_actual t ss js hj j hjj
  obtain ⟨u,hu,_,hl,hproper⟩ := component_pair_proper t ss hp s hs
  have he : (u,s) = j.problem := Option.some.inj (hu.symm.trans hps)
  rw [←he]
  have hn := multiple_sources_smaller t ss hp hmultiple s hs
  exact ⟨hproper,by simpa [hl.length_eq] using hn,hn⟩

end GenericForest
