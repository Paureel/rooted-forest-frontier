import OutputBudget

/-! One-shot all-emission color support accounting. This proof counts actual
output-list members and needs no target source partition or cut realization. -/
namespace Universal233.SourceCoverage
open RMAF CoreProgram CoreGraph Integration

def dedupNat : List Nat → List Nat
  | [] => []
  | x :: xs => let ys := dedupNat xs; if x ∈ ys then ys else x :: ys

@[simp] theorem mem_dedupNat (xs : List Nat) (x : Nat) : x ∈ dedupNat xs ↔ x ∈ xs := by
  induction xs generalizing x with
  | nil => simp [dedupNat]
  | cons a xs ih => simp only [dedupNat]; split <;> simp_all

theorem dedupNat_nodup (xs : List Nat) : (dedupNat xs).Nodup := by
  induction xs with
  | nil => simp [dedupNat]
  | cons a xs ih => simp only [dedupNat]; split <;> simp_all

def colors : GTree → List Nat
  | .leaf g => [g.color]
  | .node _ l r => colors l ++ colors r

def colorCount (t : GTree) : Nat := (dedupNat (colors t)).length

def ColorCover (t : GTree) (cs : List Nat) : Prop := ∀ i, i ∈ colors t → i ∈ cs

theorem colors_eq_groups (t : GTree) : colors t = (groups t).map Group.color := by
  induction t with
  | leaf g => rfl
  | node p l r ihl ihr => simp [colors,groups,ihl,ihr]

theorem colorCount_le_cover (t : GTree) (cs : List Nat) (h : ColorCover t cs) :
    colorCount t ≤ cs.length := by
  apply (dedupNat_nodup (colors t)).length_le_of_subset
  intro i hi
  exact h i ((mem_dedupNat (colors t) i).mp hi)

theorem normalize_color_mem (t : GTree) (i : Nat) : i ∈ colors (normalize t) ↔ i ∈ colors t := by
  induction t with
  | leaf g => rfl
  | node p l r ihl ihr =>
    cases hl : normalize l with
    | leaf a =>
      cases hr : normalize r with
      | leaf b => simp only [normalize,hl,hr]; split <;> simp_all [colors]
      | node q a b => simp_all [normalize,colors] <;> grind
    | node q a b => cases hr : normalize r <;> simp_all [normalize,colors] <;> grind

theorem normalize_colorCover (t : GTree) (cs : List Nat) (h : ColorCover (normalize t) cs) :
    ColorCover t cs := by
  intro i hi
  exact h i ((normalize_color_mem t i).mpr hi)

theorem gLeafErase_selected {t u v g} (h : GLeafErase t u v g) : GroupLeafAt t v g := by
  induction h with
  | rootLeft => rfl
  | rootRight => rfl
  | left p r h ih => exact ih
  | right p l h ih => exact ih

theorem erase_colors_cover {t u v g} (h : GLeafErase t u v g) :
    ∀ i, i ∈ colors t → i = g.color ∨ i ∈ colors u := by
  intro i hi
  rw [colors_eq_groups] at hi
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hi
  obtain ⟨w,hw⟩ := groupLeaf_of_groups_mem t a ha
  by_cases hwv : w = v
  · subst w
    have hv : GroupLeafAt t v g := gLeafErase_selected h
    have hag : a = g := Option.some.inj (hw.symm.trans hv)
    exact Or.inl (he.symm.trans (congrArg Group.color hag))
  · obtain ⟨w',hw',hew⟩ := gLeafErase_group_survives h w a hw hwv
    right
    rw [colors_eq_groups]
    exact List.mem_map.mpr ⟨a,groupLeaf_mem_groups u w' a hw',he⟩

theorem erase_colors_subset {t u v g} (h : GLeafErase t u v g) :
    ∀ i, i ∈ colors u → i ∈ colors t := by
  intro i hi
  rw [colors_eq_groups] at hi ⊢
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hi
  obtain ⟨w,hw⟩ := groupLeaf_of_groups_mem u a ha
  exact List.mem_map.mpr ⟨a,groupLeaf_mem_groups t _ a (gLeafErase_group_lift h w a hw),he⟩

theorem choose_finish_cover (t : GTree) (hc : choose t = .finish) :
    ∃ i, ColorCover t [i] := by
  cases hgs : groups t with
  | nil => exact False.elim (groups_nonempty t hgs)
  | cons first rest =>
    simp only [choose,hgs] at hc
    split at hc
    next hall =>
      refine ⟨first.color,?_⟩
      intro i hi
      rw [colors_eq_groups,hgs] at hi
      obtain ⟨a,ha,he⟩ := List.mem_map.mp hi
      have hcol := List.all_eq_true.mp hall a ha
      simp only [List.mem_singleton]
      exact he.symm.trans (beq_iff_eq.mp hcol)
    next =>
      cases hf : (first :: rest).find? (fun g => ((first :: rest).filter (fun h => h.color == g.color)).length == 1) with
      | some a => simp [hf] at hc
      | none =>
        simp only [hf] at hc
        cases hm : mixedCherry t with
        | none => simp [hm] at hc
        | some pair => cases pair; simp only [hm] at hc; split at hc <;> cases hc

theorem attempt_color_cover (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (h : ∀ t d c o, (origins t).Nodup → o ∈ (f t d c).outputs →
      ∃ cs, ColorCover t cs ∧ cs.length + c.length ≤ o.sourceCuts.length + 1)
    (t d c g o) (hn : (origins t).Nodup)
    (v : RMAF.Vertex) (hv : GroupLeafAt t v g) (hvr : v ≠ [])
    (ho : o ∈ (attempt f t d c g).outputs) :
    ∃ cs, ColorCover t cs ∧ cs.length + c.length ≤ o.sourceCuts.length + 1 := by
  unfold attempt at ho
  split at ho
  · simp at ho
  · split at ho
    · simp at ho
    · split at ho
      · simp at ho
      · rename_i u hu
        obtain ⟨u',hu',⟨herase⟩⟩ := erase_leaf_realization t hn v g hv hvr
        have he : u' = u := Option.some.inj (hu'.symm.trans hu)
        subst u'
        obtain ⟨cs,hcs,hlen⟩ := h u (g :: d) (g.origin :: c) o (erase_origins_nodup t _ u hu hn) ho
        refine ⟨g.color :: cs,?_,?_⟩
        · intro i hi
          rcases erase_colors_cover herase i hi with hi | hi
          · simp [hi]
          · exact List.mem_cons_of_mem _ (hcs i hi)
        · simp only [List.length_cons] at hlen ⊢
          omega

theorem step_color_cover (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (h : ∀ t d c o, (origins t).Nodup → o ∈ (f t d c).outputs →
      ∃ cs, ColorCover t cs ∧ cs.length + c.length ≤ o.sourceCuts.length + 1)
    (t d c o) (hn : (origins t).Nodup) (ho : o ∈ (step f t d c).outputs) :
    ∃ cs, ColorCover t cs ∧ cs.length + c.length ≤ o.sourceCuts.length + 1 := by
  have hnn := normalize_origins_nodup t hn
  have liftResult : (∃ cs, ColorCover (normalize t) cs ∧ cs.length + c.length ≤ o.sourceCuts.length + 1) →
      ∃ cs, ColorCover t cs ∧ cs.length + c.length ≤ o.sourceCuts.length + 1 := by
    rintro ⟨cs,hcs,hlen⟩
    exact ⟨cs,normalize_colorCover t cs hcs,hlen⟩
  apply liftResult
  cases hc : choose (normalize t) with
  | finish =>
    obtain ⟨i,hi⟩ := choose_finish_cover (normalize t) hc
    have he : o = ⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels],c⟩ := by
      simpa [step,hc] using ho
    exact ⟨[i],hi,by simp [he,Nat.add_comm]⟩
  | one g =>
    obtain ⟨hg,hlen⟩ := choose_one_selected (normalize t) g hc
    obtain ⟨v,hv⟩ := groupLeaf_of_groups_mem (normalize t) g hg
    exact attempt_color_cover f h _ d c g o hnn v hv
      (choose_one_nonroot (normalize t) g hc v hv) (by simpa [step,hc,prefixRoot] using ho)
  | two a b =>
    obtain ⟨p,hp,hne⟩ := choose_two_selected (normalize t) a b hc
    have hm : o ∈ (attempt f (normalize t) d c a).outputs ∨
        o ∈ (attempt f (normalize t) d c b).outputs := by simpa [step,hc,prefixRoot,combine] using ho
    rcases hm with hm | hm
    · exact attempt_color_cover f h _ d c a o hnn (p ++ [false]) (gcherry_left hp) (by simp) hm
    · exact attempt_color_cover f h _ d c b o hnn (p ++ [true]) (gcherry_right hp) (by simp) hm
  | refuse why => simp [step,hc] at ho

theorem run_color_cover (q : Nat) (t d c o) (hn : (origins t).Nodup)
    (ho : o ∈ (run q t d c).outputs) :
    ∃ cs, ColorCover t cs ∧ cs.length + c.length ≤ o.sourceCuts.length + 1 := by
  induction q generalizing t d c o with
  | zero => exact step_color_cover _ (by intros; contradiction) t d c o hn ho
  | succ q ih => exact step_color_cover (run q) (by intros; apply ih; assumption; assumption) t d c o hn ho

theorem run_color_cost (q : Nat) (t d c o) (hn : (origins t).Nodup)
    (ho : o ∈ (run q t d c).outputs) : colorCount t + c.length ≤ o.sourceCuts.length + 1 := by
  obtain ⟨cs,hcs,hlen⟩ := run_color_cover q t d c o hn ho
  have hr := colorCount_le_cover t cs hcs
  omega

theorem fromTree_colors (color : Nat → Nat) (p : RMAF.Vertex) (t : Tree) :
    colors (fromTree color p t) = (leaves t).map color := by
  induction t generalizing p with
  | leaf x => rfl
  | node l r ihl ihr => simp [fromTree,colors,leaves,ihl,ihr]

/-- Every actual emission has at least r-1 recorded cuts, where r is the
number of distinct input colors. This is all-output support accounting, not
an assertion of realized original-edge components. -/
theorem generate_color_cost (t : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate t color q).outputs) :
    (dedupNat ((leaves t).map color)).length ≤ o.sourceCuts.length + 1 := by
  unfold generate at ho
  split at ho
  · have hb := run_color_cost _ _ _ _ o (fromTree_origins_nodup color [] t) ho
    simpa only [colorCount,fromTree_colors,List.length_nil,Nat.add_zero] using hb
  · simp at ho

end Universal233.SourceCoverage
