import RMAF
namespace BinaryExchange
open RMAF

/-- One-shot general restriction lemmas for target E. -/
def joinOpt : Option Tree → Option Tree → Option Tree
  | none, none => none
  | some a, none => some a
  | none, some b => some b
  | some a, some b => some (.node a b)

theorem restrict_node (C : List Nat) (l r : Tree) :
    restrict C (.node l r) = joinOpt (restrict C l) (restrict C r) := rfl

theorem restrict_congr (t : Tree) (C D : List Nat)
    (h : ∀ x, x ∈ leaves t → (x ∈ C ↔ x ∈ D)) : restrict C t = restrict D t := by
  induction t with
  | leaf x =>
    have hx := h x (by simp [leaves])
    simp only [restrict, List.contains_iff_mem]
    simp [hx]
  | node l r hl hr =>
    rw [restrict_node, restrict_node, hl, hr]
    · intro x hx; exact h x (by simp [leaves, hx])
    · intro x hx; exact h x (by simp [leaves, hx])

theorem restrict_none_iff (C : List Nat) (t : Tree) :
    restrict C t = none ↔ ∀ x, x ∈ leaves t → x ∉ C := by
  induction t with
  | leaf x => simp [restrict, leaves]
  | node l r hl hr =>
    cases el : restrict C l <;> cases er : restrict C r <;>
      simp_all [restrict, leaves] <;> grind

theorem restrict_mem (C : List Nat) (t u : Tree) (h : restrict C t = some u) (x : Nat) :
    x ∈ leaves u ↔ x ∈ leaves t ∧ x ∈ C := by
  induction t generalizing u with
  | leaf y =>
    by_cases hy : y ∈ C
    · have eu : u = .leaf y := by simpa [restrict, hy] using h.symm
      subst u; simp [leaves, hy]; grind
    · simp [restrict, hy] at h
  | node l r hl hr =>
    cases el : restrict C l <;> cases er : restrict C r
    · simp [restrict, el, er] at h
    · have eu : u = _ := Option.some.inj (by simpa [restrict, el, er] using h.symm)
      subst u
      have hn := (restrict_none_iff C l).1 el x
      rw [hr _ er]
      simp only [leaves, List.mem_append]
      grind
    · have eu : u = _ := Option.some.inj (by simpa [restrict, el, er] using h.symm)
      subst u
      have hn := (restrict_none_iff C r).1 er x
      rw [hl _ el]
      simp only [leaves, List.mem_append]
      grind
    · have eu : u = _ := Option.some.inj (by simpa [restrict, el, er] using h.symm)
      subst u
      simp only [leaves, List.mem_append, hl _ el, hr _ er]
      grind

theorem restrict_joinOpt (D : List Nat) (a b : Option Tree) :
    (joinOpt a b).bind (restrict D) =
      joinOpt (a.bind (restrict D)) (b.bind (restrict D)) := by
  cases a <;> cases b <;> simp [joinOpt, restrict, Option.bind] <;>
    split <;> simp_all [joinOpt]

theorem restrict_filter (C D : List Nat) (t : Tree) :
    (restrict C t).bind (restrict D) = restrict (C.filter (D.contains ·)) t := by
  induction t with
  | leaf x =>
    by_cases hc : x ∈ C <;> by_cases hd : x ∈ D <;> simp [restrict, hc, hd]
  | node l r hl hr =>
    simp only [restrict_node, restrict_joinOpt, hl, hr]

theorem restrict_subset (C D : List Nat) (t u : Tree)
    (h : ∀ x, x ∈ D → x ∈ C) (hu : restrict C t = some u) :
    restrict D u = restrict D t := by
  have hf := restrict_filter C D t
  rw [hu] at hf
  simp only [Option.bind_some] at hf
  exact hf.trans (restrict_congr t _ D (by
    intro x hx
    simp only [List.mem_filter, List.contains_iff_mem]
    exact ⟨fun p => p.2, fun hd => ⟨h x hd, hd⟩⟩))

theorem iso_symm {s t : Tree} (h : RootedIso s t) : RootedIso t s := by
  induction h with
  | leaf x => exact .leaf x
  | straight h1 h2 ih1 ih2 => exact .straight ih1 ih2
  | swapped h1 h2 ih1 ih2 => exact .swapped ih2 ih1

theorem iso_leaves {s t : Tree} (h : RootedIso s t) (x : Nat) :
    x ∈ leaves s ↔ x ∈ leaves t := by
  induction h with
  | leaf y => rfl
  | straight h1 h2 ih1 ih2 => simp only [leaves, List.mem_append, ih1, ih2]
  | swapped h1 h2 ih1 ih2 => simp only [leaves, List.mem_append, ih1, ih2]; exact or_comm

def OptIso : Option Tree → Option Tree → Prop
  | none, none => True
  | some s, some t => RootedIso s t
  | _, _ => False

theorem optIso_join {a b c d : Option Tree} (ha : OptIso a c) (hb : OptIso b d) :
    OptIso (joinOpt a b) (joinOpt c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [OptIso, joinOpt]
  exact .straight ha hb

theorem optIso_join_swap {a b c d : Option Tree} (ha : OptIso a d) (hb : OptIso b c) :
    OptIso (joinOpt a b) (joinOpt c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [OptIso, joinOpt]
  exact .swapped ha hb

theorem iso_restrict {s t : Tree} (h : RootedIso s t) (C : List Nat) :
    OptIso (restrict C s) (restrict C t) := by
  induction h with
  | leaf x => by_cases hx : x ∈ C <;> simp [restrict, hx, OptIso, RootedIso.leaf]
  | straight h1 h2 ih1 ih2 => exact optIso_join ih1 ih2
  | swapped h1 h2 ih1 ih2 => exact optIso_join_swap ih1 ih2

theorem restrictionAgrees_sub (s t : Tree) (C D : List Nat)
    (h : restrictionAgrees s t C = true) (hsub : ∀ x, x ∈ D → x ∈ C)
    (hne : ∃ x, x ∈ D ∧ x ∈ leaves s) : restrictionAgrees s t D = true := by
  unfold restrictionAgrees at h ⊢
  cases es : restrict C s <;> cases et : restrict C t <;> simp only [es,et] at h
  all_goals try contradiction
  rename_i ss tt
  have hi : RootedIso ss tt := (sameShape_correct _ _).1 h
  have hr := iso_restrict hi D
  rw [restrict_subset C D s ss hsub es, restrict_subset C D t tt hsub et] at hr
  cases ds : restrict D s <;> cases dt : restrict D t
  · obtain ⟨x,hx,hxs⟩ := hne
    exact False.elim ((restrict_none_iff D s).1 ds x hxs hx)
  · simp [ds,dt,OptIso] at hr
  · simp [ds,dt,OptIso] at hr
  · exact (sameShape_correct _ _).2 (by simpa [ds,dt,OptIso] using hr)

end BinaryExchange
