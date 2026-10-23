import ColorBudget

/-! One-shot chooser-sensitive distinct-color change for actual erase. -/
namespace Universal233.SourceCoverage
open RMAF CoreProgram CoreGraph Integration

theorem colorCount_pos (t : GTree) : 0 < colorCount t := by
  cases hg : groups t with
  | nil => exact False.elim (groups_nonempty t hg)
  | cons g rest =>
    have hm : g.color ∈ colors t := by simp [colors_eq_groups,hg]
    exact List.length_pos_of_mem ((mem_dedupNat (colors t) g.color).mpr hm)

theorem colorCount_normalize (t : GTree) : colorCount (normalize t) = colorCount t := by
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup (dedupNat_nodup _) (dedupNat_nodup _)).mpr
  intro i
  simp only [mem_dedupNat,normalize_color_mem]

theorem erase_colorCount_one {t u v g} (h : GLeafErase t u v g) : colorCount t ≤ colorCount u + 1 := by
  have hc : ColorCover t (g.color :: dedupNat (colors u)) := by
    intro i hi
    rcases erase_colors_cover h i hi with hi | hi
    · simp [hi]
    · exact List.mem_cons_of_mem _ ((mem_dedupNat (colors u) i).mpr hi)
  have hl := colorCount_le_cover t _ hc
  simpa only [List.length_cons,Nat.add_comm,colorCount] using hl

theorem groups_nodup (t : GTree) (hn : (origins t).Nodup) : (groups t).Nodup := by
  induction t with
  | leaf g => simp [groups]
  | node p l r ihl ihr =>
    obtain ⟨hpn,hnlr⟩ := List.nodup_cons.mp hn
    obtain ⟨hnl,hnr,hdisj⟩ := List.nodup_append.mp hnlr
    apply List.nodup_append.mpr
    refine ⟨ihl hnl,ihr hnr,?_⟩
    intro a ha b hb he
    obtain ⟨va,hva⟩ := groupLeaf_of_groups_mem l a ha
    obtain ⟨vb,hvb⟩ := groupLeaf_of_groups_mem r b hb
    exact hdisj a.origin (groupLeaf_origin_mem l va a hva) b.origin
      (groupLeaf_origin_mem r vb b hvb) (congrArg Group.origin he)

theorem choose_two_nonunique (t : GTree) (a b g : Group)
    (hc : choose t = .two a b) (hg : g ∈ groups t) :
    ((groups t).filter (fun h => h.color == g.color)).length ≠ 1 := by
  cases hgs : groups t with
  | nil => simp [hgs] at hg
  | cons first rest =>
    simp only [choose,hgs] at hc
    split at hc
    next => cases hc
    next =>
      cases hf : (first :: rest).find? (fun g => ((first :: rest).filter (fun h => h.color == g.color)).length == 1) with
      | some x => simp [hf] at hc
      | none =>
        have hh := List.find?_eq_none.mp hf g (by simpa only [hgs] using hg)
        simpa only [beq_iff_eq,hgs] using hh

theorem nonunique_other (t : GTree) (g : Group) (hn : (origins t).Nodup)
    (hg : g ∈ groups t)
    (hu : ((groups t).filter (fun h => h.color == g.color)).length ≠ 1) :
    ∃ a, a ∈ groups t ∧ a.color = g.color ∧ a ≠ g := by
  classical
  apply Classical.byContradiction
  intro hno
  have hall : ∀ a, a ∈ groups t → a.color = g.color → a = g := by
    intro a ha hc
    apply Classical.byContradiction
    intro he
    exact hno ⟨a,ha,hc,he⟩
  have hfilterNodup := (groups_nodup t hn).filter (fun h => h.color == g.color)
  have hsub : (groups t).filter (fun h => h.color == g.color) ⊆ [g] := by
    intro a ha
    obtain ⟨ha,hc⟩ := List.mem_filter.mp ha
    simp only [List.mem_singleton]
    exact hall a ha (beq_iff_eq.mp hc)
  have hle := List.Nodup.length_le_of_subset hfilterNodup hsub
  have hmem : g ∈ (groups t).filter (fun h => h.color == g.color) := by simp [hg]
  have hpos := List.length_pos_of_mem hmem
  have hone : ((groups t).filter (fun h => h.color == g.color)).length = 1 := by
    simp only [List.length_singleton] at hle
    omega
  exact hu hone

theorem erase_colorCount_two {t u v g} (h : GLeafErase t u v g)
    (hn : (origins t).Nodup)
    (hu : ((groups t).filter (fun h => h.color == g.color)).length ≠ 1) :
    colorCount t ≤ colorCount u := by
  have hvg := gLeafErase_selected h
  obtain ⟨a,ha,hcol,hag⟩ := nonunique_other t g hn (groupLeaf_mem_groups t v g hvg) hu
  obtain ⟨w,hw⟩ := groupLeaf_of_groups_mem t a ha
  have hwv : w ≠ v := by
    intro he
    subst w
    exact hag (Option.some.inj (hw.symm.trans hvg))
  obtain ⟨w',hw',hew⟩ := gLeafErase_group_survives h w a hw hwv
  have hgc : g.color ∈ colors u := by
    rw [colors_eq_groups]
    exact List.mem_map.mpr ⟨a,groupLeaf_mem_groups u w' a hw',hcol⟩
  apply colorCount_le_cover t (dedupNat (colors u))
  intro i hi
  apply (mem_dedupNat (colors u) i).mpr
  rcases erase_colors_cover h i hi with hi | hi
  · simpa only [hi] using hgc
  · exact hi

theorem run_color_budget_empty (q : Nat) (t d c) (hn : (origins t).Nodup)
    (hshort : q + 1 < colorCount t) : (run q t d c).outputs = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro o ho
  have hc := run_color_cost q t d c o hn ho
  have hb := run_output_budget q t d c o ho
  omega

end Universal233.SourceCoverage
