import RestrictionCounts
import ForwardNormal

namespace TripleDP.Transitions.Restriction
open TripleDP.CostRoute

variable {α I J : Type} {l r : BTree α}

def Represents {t : BTree α} (G : Family t J) (A : Family t I) (f : J → I) : Prop :=
  (∀ j k, f j = f k → j = k) ∧
  (∀ i, ∃ j, f j = i) ∧
  (∀ j, G.support j = A.support (f j)) ∧
  Option.map f G.boundary = A.boundary

def splitMap (A : Family (.node l r) I) :
    Sum (LiveIndex A false) (LiveIndex A true) → I
  | .inl i => i.val
  | .inr i => i.val

theorem splitMap_surjective (A : Family (.node l r) I) :
    ∀ i, ∃ j, splitMap A j = i := by
  intro i
  rcases live_some_child A i with hl | hr
  · exact ⟨.inl ⟨i, hl⟩, rfl⟩
  · exact ⟨.inr ⟨i, hr⟩, rfl⟩

theorem splitMap_injective (A : Family (.node l r) I)
    (hn : ¬ ∃ i, Live A false i ∧ Live A true i) :
    ∀ j k, splitMap A j = splitMap A k → j = k := by
  intro j k he
  cases j with
  | inl j =>
    cases k with
    | inl k => exact congrArg Sum.inl (Subtype.ext he)
    | inr k => exact False.elim (hn ⟨j.val, j.property, he.symm ▸ k.property⟩)
  | inr j =>
    cases k with
    | inl k => exact False.elim (hn ⟨k.val, k.property, he ▸ j.property⟩)
    | inr k => exact congrArg Sum.inr (Subtype.ext he)

theorem not_live_no_support (A : Family (.node l r) I) (h : OpenBranchLive A)
    (i : I) (side : Bool) (hn : ¬ Live A side i) (a : Address) :
    ¬ A.support i (side :: a) := fun ha => hn (occupied_live A h i side ⟨a, ha⟩)

theorem support_left_exact (A : Family (.node l r) I) (h : OpenBranchLive A)
    (i : I) (hn : ¬ Live A true i) :
    A.support i = fun a => (A.boundary = some i ∧ a = []) ∨
      liftSupport false (fun b => A.support i (false :: b)) a := by
  funext a
  apply propext
  cases a with
  | nil => rw [A.root_spec]; simp [liftSupport]
  | cons side a =>
    cases side with
    | false => simp [liftSupport]
    | true => simp [liftSupport, not_live_no_support A h i true hn a]

theorem support_right_exact (A : Family (.node l r) I) (h : OpenBranchLive A)
    (i : I) (hn : ¬ Live A false i) :
    A.support i = fun a => (A.boundary = some i ∧ a = []) ∨
      liftSupport true (fun b => A.support i (true :: b)) a := by
  funext a
  apply propext
  cases a with
  | nil => rw [A.root_spec]; simp [liftSupport]
  | cons side a =>
    cases side with
    | false => simp [liftSupport, not_live_no_support A h i false hn a]
    | true => simp [liftSupport]

theorem no_overlap_closed (A : Family (.node l r) I) (ho : A.boundary = none) :
    ¬ ∃ i, Live A false i ∧ Live A true i := by
  rintro ⟨i, hl, hr⟩
  have hi := both_live_boundary A i hl hr
  simp [ho] at hi

theorem no_overlap_left (A : Family (.node l r) I) (o : I)
    (ho : A.boundary = some o) (hr : ¬ Live A true o) :
    ¬ ∃ i, Live A false i ∧ Live A true i := by
  intro hi
  exact hr ((overlap_iff_open A o ho).mp hi).2

theorem no_overlap_right (A : Family (.node l r) I) (o : I)
    (ho : A.boundary = some o) (hl : ¬ Live A false o) :
    ¬ ∃ i, Live A false i ∧ Live A true i := by
  intro hi
  exact hl ((overlap_iff_open A o ho).mp hi).1

theorem represents_labels {t : BTree α} (G : Family t J) (A : Family t I)
    (f : J → I) (hf : Represents G A f) (j : J) (x : α) :
    G.hasLabel j x ↔ A.hasLabel (f j) x := by
  unfold Family.hasLabel
  rw [hf.2.2.1 j]

#print axioms splitMap_surjective
#print axioms splitMap_injective
#print axioms not_live_no_support
#print axioms support_left_exact
#print axioms support_right_exact
#print axioms no_overlap_closed
#print axioms no_overlap_left
#print axioms no_overlap_right
#print axioms represents_labels
end TripleDP.Transitions.Restriction
