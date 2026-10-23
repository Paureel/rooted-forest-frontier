import RMAF

/-! One-shot literal original-tree restriction proofs. No transport assumptions. -/
namespace RestrictionBridge
open RMAF

def join : Option Tree → Option Tree → Option Tree
  | none, none => none
  | some a, none => some a
  | none, some b => some b
  | some a, some b => some (.node a b)

theorem restrict_node (U : List Nat) (l r : Tree) :
    restrict U (.node l r) = join (restrict U l) (restrict U r) := rfl

theorem join_bind (a b : Option Tree) (B : List Nat) :
    (join a b).bind (restrict B) = join (a.bind (restrict B)) (b.bind (restrict B)) := by
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases h : restrict B b <;> simp [join, h]
  | some a => cases b with
    | none => cases h : restrict B a <;> simp [join, h]
    | some b => rfl

theorem restrict_compose_mask (t : Tree) (U B C : List Nat)
    (mask : ∀ x, C.contains x = (U.contains x && B.contains x)) :
    (restrict U t).bind (restrict B) = restrict C t := by
  induction t with
  | leaf x =>
    have hm : x ∈ C ↔ x ∈ U ∧ x ∈ B := by
      have hh := congrArg (fun b => b = true) (mask x)
      apply Iff.of_eq
      simpa only [Bool.and_eq_true, List.contains_iff_mem] using hh
    by_cases hu : x ∈ U <;> by_cases hb : x ∈ B <;> simp [restrict, hm, hu, hb]
  | node l r hl hr =>
    rw [restrict_node, restrict_node, join_bind, hl, hr]

theorem restrict_nested (t : Tree) (U B : List Nat) (sub : B ⊆ U) :
    (restrict U t).bind (restrict B) = restrict B t := by
  apply restrict_compose_mask
  intro x
  by_cases h : x ∈ B
  · have hu := sub h
    simp only [List.contains_iff_mem.mpr h, List.contains_iff_mem.mpr hu]
    rfl
  · simp [h]

theorem restrict_inside (t u : Tree) (U B : List Nat)
    (hr : restrict U t = some u) (sub : B ⊆ U) : restrict B u = restrict B t := by
  simpa [hr] using restrict_nested t U B sub

def optionLeaves : Option Tree → List Nat
  | none => []
  | some t => leaves t

theorem join_leaves (a b : Option Tree) :
    optionLeaves (join a b) = optionLeaves a ++ optionLeaves b := by
  cases a <;> cases b <;> simp [optionLeaves, join, leaves]

theorem restrict_leaves (t : Tree) (U : List Nat) :
    optionLeaves (restrict U t) = (leaves t).filter (U.contains ·) := by
  induction t with
  | leaf x => by_cases hx : x ∈ U <;> simp [restrict, hx, leaves, optionLeaves]
  | node l r hl hr => simp only [restrict_node, join_leaves, hl, hr, leaves, List.filter_append]

theorem restrict_labels (t u : Tree) (U : List Nat) (hr : restrict U t = some u) :
    leaves u = (leaves t).filter (U.contains ·) := by
  simpa [hr, optionLeaves] using restrict_leaves t U

theorem leaves_nonempty (t : Tree) : leaves t ≠ [] := by
  induction t with
  | leaf x => simp [leaves]
  | node l r hl hr => simp [leaves, hl]

theorem restriction_exists (t : Tree) (U : List Nat)
    (h : ∃ x, x ∈ leaves t ∧ x ∈ U) : ∃ u, restrict U t = some u := by
  cases hr : restrict U t with
  | some u => exact ⟨u,rfl⟩
  | none =>
    obtain ⟨x,hx,hu⟩ := h
    have hf := restrict_leaves t U
    have hm : x ∈ (leaves t).filter (U.contains ·) := by simp [hx,hu]
    rw [←hf,hr] at hm
    simp [optionLeaves] at hm

theorem restricted_labels_exact (t u : Tree) (U : List Nat) (hr : restrict U t = some u)
    {x : Nat} : x ∈ leaves u ↔ x ∈ leaves t ∧ x ∈ U := by
  rw [restrict_labels t u U hr]
  simp

theorem restricted_nodup (t u : Tree) (U : List Nat) (hr : restrict U t = some u)
    (proper : (leaves t).Nodup) : (leaves u).Nodup := by
  rw [restrict_labels t u U hr]
  exact proper.filter _

theorem sameShape_restrict_inside (T S t s : Tree) (U B : List Nat)
    (ht : restrict U T = some t) (hs : restrict U S = some s) (sub : B ⊆ U) :
    restrictionAgrees t s B = restrictionAgrees T S B := by
  simp only [restrictionAgrees, restrict_inside T t U B ht sub,
    restrict_inside S s U B hs sub]

end RestrictionBridge
