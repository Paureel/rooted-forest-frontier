import Origins

/-! One-shot exact executable branch consumers, with actual leaf occurrences
and singleton obligations obtained from choose rather than supplied by a field. -/
namespace Universal233.Integration
open RMAF CoreGraph CoreProgram

theorem groupLeaf_of_groups_mem (t : GTree) (g : Group) (hg : g ∈ groups t) :
    ∃ v, GroupLeafAt t v g := by
  induction t with
  | leaf a => have he : g = a := by simpa [groups] using hg
              subst g; exact ⟨[],rfl⟩
  | node p l r ihl ihr =>
    simp only [groups,List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨v,hv⟩ := ihl hg; exact ⟨false :: v,hv⟩
    · obtain ⟨v,hv⟩ := ihr hg; exact ⟨true :: v,hv⟩

theorem groupLeaf_mem_groups (t : GTree) (v : RMAF.Vertex) (g : Group)
    (hv : GroupLeafAt t v g) : g ∈ groups t := by
  induction t generalizing v with
  | leaf a => obtain ⟨rfl,rfl⟩ := (groupLeaf_leaf a g v).1 hv; simp [groups]
  | node p l r ihl ihr =>
    cases v with
    | nil => simp [GroupLeafAt,groupAt] at hv
    | cons s v => cases s <;> simp only [groups,List.mem_append]
                             <;> first | exact Or.inl (ihl v hv) | exact Or.inr (ihr v hv)

theorem skeleton_leaf_group (t : GTree) (v : RMAF.Vertex) (c : Nat) (hv : LeafAt (skeleton t) v c) :
    ∃ g, GroupLeafAt t v g ∧ g.color = c := by
  induction t generalizing v with
  | leaf a =>
    cases v with
    | nil => exact ⟨a,rfl,by simpa [LeafAt,skeleton,subtree] using hv⟩
    | cons s v => simp [LeafAt,skeleton,subtree] at hv
  | node p l r ihl ihr =>
    cases v with
    | nil => simp [LeafAt,skeleton,subtree] at hv
    | cons s v => cases s <;> first | exact ihl v hv | exact ihr v hv

theorem groupLeaf_address_unique (t : GTree) (hn : (origins t).Nodup)
    (v w : RMAF.Vertex) (g : Group) (hv : GroupLeafAt t v g) (hw : GroupLeafAt t w g) : v = w := by
  induction t generalizing v w with
  | leaf a => exact ((groupLeaf_leaf a g v).1 hv).1.trans ((groupLeaf_leaf a g w).1 hw).1.symm
  | node p l r ihl ihr =>
    obtain ⟨hpn,hnc⟩ := List.nodup_cons.1 hn
    obtain ⟨hnl,hnr,hdisj⟩ := List.nodup_append.1 hnc
    cases v with
    | nil => simp [GroupLeafAt,groupAt] at hv
    | cons s v =>
      cases w with
      | nil => simp [GroupLeafAt,groupAt] at hw
      | cons z w =>
        cases s <;> cases z
        · exact congrArg (false :: ·) (ihl hnl v w hv hw)
        · exact False.elim (hdisj _ (groupLeaf_origin_mem l v g hv) _ (groupLeaf_origin_mem r w g hw) rfl)
        · exact False.elim (hdisj _ (groupLeaf_origin_mem l w g hw) _ (groupLeaf_origin_mem r v g hv) rfl)
        · exact congrArg (true :: ·) (ihr hnr v w hv hw)

theorem choose_one_selected (t : GTree) (g : Group) (hc : choose t = .one g) :
    g ∈ groups t ∧ ((groups t).filter (fun h => h.color == g.color)).length = 1 := by
  cases hgs : groups t with
  | nil => simp [choose,hgs] at hc
  | cons a rest =>
    simp only [choose,hgs] at hc
    split at hc
    next => cases hc
    next =>
      cases hf : (a :: rest).find? (fun g => ((a :: rest).filter (fun h => h.color == g.color)).length == 1) with
      | some b =>
        simp only [hf] at hc
        have he : b = g := by cases hc; rfl
        subst b
        have hh : ((a :: rest).filter (fun h => h.color == g.color)).length == 1 :=
          List.find?_some (p := fun g : Group => ((a :: rest).filter (fun h => h.color == g.color)).length == 1) (a := g) hf
        exact ⟨by simpa only [hgs] using List.mem_of_find?_eq_some hf,
          by simpa only [hgs] using beq_iff_eq.1 hh⟩
      | none =>
        simp only [hf] at hc
        cases hm : mixedCherry t with
        | none => simp [hm] at hc
        | some pair => cases pair with
          | mk a b => simp only [hm] at hc; split at hc <;> cases hc

theorem choose_one_nonroot (t : GTree) (g : Group) (hc : choose t = .one g)
    (v : RMAF.Vertex) (hv : GroupLeafAt t v g) : v ≠ [] := by
  intro he; subst v
  cases t with
  | leaf a => simp [choose,groups] at hc
  | node p l r => simp [GroupLeafAt,groupAt] at hv

theorem unique_filter_group (t : GTree) (g a : Group)
    (hg : g ∈ groups t) (ha : a ∈ groups t)
    (hc : a.color = g.color)
    (hlen : ((groups t).filter (fun h => h.color == g.color)).length = 1) : a = g := by
  obtain ⟨b,hb⟩ := List.length_eq_one_iff.1 hlen
  have hgm : g ∈ (groups t).filter (fun h => h.color == g.color) := by simp [hg]
  have ham : a ∈ (groups t).filter (fun h => h.color == g.color) := by simp [ha,hc]
  rw [hb] at hgm ham
  simp only [List.mem_singleton] at hgm ham
  exact ham.trans hgm.symm

/-- Exact unique-color branch of choose supplies the actual graph singleton,
selected occurrence, and nonroot premise needed by the proved erase consumer. -/
theorem choose_one_source_singleton (t : GTree) (hn : (origins t).Nodup)
    (P : SourcePartition (skeleton t)) (hm : Monochromatic P id)
    (g : Group) (hc : choose t = .one g) :
    ∃ v, GroupLeafAt t v g ∧ v ≠ [] ∧ SingletonBlock P v := by
  obtain ⟨hg,hfilter⟩ := choose_one_selected t g hc
  obtain ⟨v,hv⟩ := groupLeaf_of_groups_mem t g hg
  refine ⟨v,hv,choose_one_nonroot t g hc v hv,?_⟩
  apply unique_color_singleton P (groupLeaf_skeleton t v g hv) id hm
  intro w c hw hcolor
  obtain ⟨a,ha,hac⟩ := skeleton_leaf_group t w c hw
  have hcol : a.color = g.color := hac.trans hcolor
  have he := unique_filter_group t g a hg (groupLeaf_mem_groups t w a ha) hcol hfilter
  subst a
  exact groupLeaf_address_unique t hn w v g ha hv

inductive GCherryAt : GTree → RMAF.Vertex → Group → Group → Prop
  | root (p : RMAF.Vertex) (a b : Group) : GCherryAt (.node p (.leaf a) (.leaf b)) [] a b
  | left {t v a b} (p : RMAF.Vertex) (r : GTree) : GCherryAt t v a b →
      GCherryAt (.node p t r) (false :: v) a b
  | right {t v a b} (p : RMAF.Vertex) (l : GTree) : GCherryAt t v a b →
      GCherryAt (.node p l t) (true :: v) a b

theorem gcherry_graph {t p a b} (h : GCherryAt t p a b) :
    CherryAt (skeleton t) p a.color b.color := by
  induction h with
  | root => rfl
  | left p r h ih => exact ih
  | right p l h ih => exact ih

theorem gcherry_left {t p a b} (h : GCherryAt t p a b) : GroupLeafAt t (p ++ [false]) a := by
  induction h with
  | root => rfl
  | left p r h ih => exact ih
  | right p l h ih => exact ih

theorem gcherry_right {t p a b} (h : GCherryAt t p a b) : GroupLeafAt t (p ++ [true]) b := by
  induction h with
  | root => rfl
  | left p r h ih => exact ih
  | right p l h ih => exact ih

theorem option_or_some {α : Type} (a b : Option α) (x : α) (h : a.or b = some x) :
    a = some x ∨ b = some x := by
  cases a with
  | none => exact Or.inr h
  | some y => exact Or.inl h

theorem mixedCherry_selected (t : GTree) (a b : Group) (h : mixedCherry t = some (a,b)) :
    ∃ p, GCherryAt t p a b := by
  induction t with
  | leaf g => simp [mixedCherry] at h
  | node p l r ihl ihr =>
    cases l with
    | leaf x =>
      cases r with
      | leaf y =>
        have he : (x,y) = (a,b) := Option.some.inj h
        cases he
        exact ⟨[],.root p a b⟩
      | node q s u =>
        change (mixedCherry (.leaf x)).or (mixedCherry (.node q s u)) = some (a,b) at h
        rcases option_or_some _ _ _ h with hl | hr
        · simp [mixedCherry] at hl
        · obtain ⟨v,hv⟩ := ihr hr; exact ⟨true :: v,.right p (.leaf x) hv⟩
    | node q s u =>
      change (mixedCherry (.node q s u)).or (mixedCherry r) = some (a,b) at h
      rcases option_or_some _ _ _ h with hl | hr
      · obtain ⟨v,hv⟩ := ihl hl; exact ⟨false :: v,.left p r hv⟩
      · obtain ⟨v,hv⟩ := ihr hr; exact ⟨true :: v,.right p (.node q s u) hv⟩

theorem choose_two_selected (t : GTree) (a b : Group) (hc : choose t = .two a b) :
    ∃ p, GCherryAt t p a b ∧ a.color ≠ b.color := by
  cases hgs : groups t with
  | nil => simp [choose,hgs] at hc
  | cons first rest =>
    simp only [choose,hgs] at hc
    split at hc
    next => cases hc
    next =>
      cases hf : (first :: rest).find? (fun g => ((first :: rest).filter (fun h => h.color == g.color)).length == 1) with
      | some g => simp [hf] at hc
      | none =>
        simp only [hf] at hc
        cases hm : mixedCherry t with
        | none => simp [hm] at hc
        | some pair => cases pair with
          | mk x y =>
            simp only [hm] at hc
            split at hc
            next => cases hc
            next hne =>
              have he : x = a ∧ y = b := by cases hc; exact ⟨rfl,rfl⟩
              obtain ⟨rfl,rfl⟩ := he
              obtain ⟨p,hp⟩ := mixedCherry_selected t x y hm
              exact ⟨p,hp,fun heq => hne (by simpa only [beq_iff_eq] using heq)⟩

/-- Exact mixed-cherry branch of choose has one of its two actual source
singletons; both candidate cut leaves are current nonroot occurrences. -/
theorem choose_two_source_singleton (t : GTree) (P : SourcePartition (skeleton t))
    (hm : Monochromatic P id) (a b : Group) (hc : choose t = .two a b) :
    ∃ v g, (g = a ∨ g = b) ∧ GroupLeafAt t v g ∧ v ≠ [] ∧ SingletonBlock P v := by
  obtain ⟨p,hp,hneq⟩ := choose_two_selected t a b hc
  have hs := mixed_cherry_singleton P (gcherry_graph hp) id hm hneq
  rcases hs with hs | hs
  · exact ⟨p ++ [false],a,Or.inl rfl,gcherry_left hp,by simp,hs⟩
  · exact ⟨p ++ [true],b,Or.inr rfl,gcherry_right hp,by simp,hs⟩

def FullyNormalized : GTree → Prop
  | .leaf _ => True
  | .node _ l r => FullyNormalized l ∧ FullyNormalized r ∧
      ∀ a b, l = .leaf a → r = .leaf b → a.color ≠ b.color

theorem normalize_fullyNormalized (t : GTree) : FullyNormalized (normalize t) := by
  induction t with
  | leaf g => trivial
  | node p l r ihl ihr =>
    cases hl : normalize l with
    | leaf a =>
      cases hr : normalize r with
      | leaf b => simp only [normalize,hl,hr]; split <;> simp_all [FullyNormalized]
      | node q a b => simp only [normalize,hl,hr]; simp_all [FullyNormalized]
    | node q a b => cases hr : normalize r <;> simp only [normalize,hl,hr] <;> simp_all [FullyNormalized]

theorem normalized_cherry_mixed {t p a b} (h : GCherryAt t p a b) (hn : FullyNormalized t) :
    a.color ≠ b.color := by
  induction h with
  | root p a b => exact hn.2.2 a b rfl rfl
  | left p r h ih => exact ih hn.1
  | right p l h ih => exact ih hn.2.1

theorem mixedCherry_complete (t : GTree) :
    (∃ g, t = .leaf g) ∨ ∃ a b, mixedCherry t = some (a,b) := by
  induction t with
  | leaf g => exact Or.inl ⟨g,rfl⟩
  | node p l r ihl ihr =>
    rcases ihl with ⟨a,rfl⟩ | ⟨a,b,hab⟩
    · rcases ihr with ⟨b,rfl⟩ | ⟨b,c,hbc⟩
      · exact Or.inr ⟨a,b,rfl⟩
      · right
        cases r with
        | leaf b => simp [mixedCherry] at hbc
        | node q s u => exact ⟨b,c,by change (mixedCherry (.leaf a)).or _ = _; simpa [mixedCherry] using hbc⟩
    · right
      cases l with
      | leaf g => simp [mixedCherry] at hab
      | node q s u => exact ⟨a,b,by change (mixedCherry (.node q s u)).or _ = _; simp [hab]⟩

theorem groups_nonempty (t : GTree) : groups t ≠ [] := by
  induction t with
  | leaf g => simp [groups]
  | node p l r ihl ihr => simp_all [groups]

/-- The exact normalized chooser has no unsupported refusal path. -/
theorem choose_normalized_no_refusal (t : GTree) (hn : FullyNormalized t) (why : String) :
    choose t ≠ .refuse why := by
  intro hc
  have horig := hc
  cases hgs : groups t with
  | nil => exact groups_nonempty t hgs
  | cons a rest =>
    simp only [choose,hgs] at hc
    split at hc
    next => cases hc
    next =>
      cases hf : (a :: rest).find? (fun g => ((a :: rest).filter (fun h => h.color == g.color)).length == 1) with
      | some g => simp [hf] at hc
      | none =>
        simp only [hf] at hc
        cases hm : mixedCherry t with
        | none =>
          rcases mixedCherry_complete t with ⟨g,he⟩ | ⟨a,b,he⟩
          · subst t; simp [choose,groups] at horig
          · rw [hm] at he; cases he
        | some pair => cases pair with
          | mk x y =>
            obtain ⟨p,hp⟩ := mixedCherry_selected t x y hm
            have hne := normalized_cherry_mixed hp hn
            simp [hm,hne] at hc

end Universal233.Integration
