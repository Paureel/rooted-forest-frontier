import RestrictionDefs

namespace TripleDP.Transitions.Restriction
open TripleDP.CostRoute

variable {α I : Type} {l r : BTree α}

theorem cross_root (A : Family (.node l r) I) (i : I)
    (side other : Bool) (a b : Address) (hne : side ≠ other)
    (ha : A.support i (side :: a)) (hb : A.support i (other :: b)) :
    A.support i [] := by
  apply A.convex i (side :: a) (other :: b) ha hb []
  simp [OnPath, lca, hne]

theorem live_some_child (A : Family (.node l r) I) (i : I) :
    Live A false i ∨ Live A true i := by
  rcases A.labelled i with ⟨a, x, hx, hi⟩
  cases a with
  | nil => exact False.elim hx
  | cons side a =>
    cases side with
    | false => exact Or.inl ⟨a, x, hx, hi⟩
    | true => exact Or.inr ⟨a, x, hx, hi⟩

theorem occupied_live (A : Family (.node l r) I) (h : OpenBranchLive A)
    (i : I) (side : Bool) (ha : ∃ a, A.support i (side :: a)) : Live A side i := by
  by_cases ho : A.boundary = some i
  · exact h i ho side ha
  · rcases ha with ⟨a, ha⟩
    rcases A.labelled i with ⟨b, x, hx, hb⟩
    cases b with
    | nil => exact False.elim hx
    | cons other b =>
      by_cases he : side = other
      · subst other
        exact ⟨b, x, by cases side <;> exact hx, hb⟩
      · exact False.elim (ho ((A.root_spec i).mp
          (cross_root A i side other a b he ha hb)))

theorem live_iff_occupied (A : Family (.node l r) I) (h : OpenBranchLive A)
    (i : I) (side : Bool) :
    Live A side i ↔ ∃ a, A.support i (side :: a) := by
  constructor
  · rintro ⟨a, _, _, ha⟩; exact ⟨a, ha⟩
  · exact occupied_live A h i side

theorem both_live_boundary (A : Family (.node l r) I) (i : I)
    (hl : Live A false i) (hr : Live A true i) : A.boundary = some i := by
  rcases hl with ⟨a, _, _, ha⟩
  rcases hr with ⟨b, _, _, hb⟩
  exact (A.root_spec i).mp (cross_root A i false true a b (by decide) ha hb)

theorem open_live_child_root (A : Family (.node l r) I) (o : I)
    (ho : A.boundary = some o) (side : Bool) (h : Live A side o) :
    A.support o [side] := by
  rcases h with ⟨a, _, _, ha⟩
  exact rooted_child_contains_root (A.support o) (A.convex o)
    ((A.root_spec o).mpr ho) side ⟨a, ha⟩

#print axioms cross_root
#print axioms live_some_child
#print axioms occupied_live
#print axioms live_iff_occupied
#print axioms both_live_boundary
#print axioms open_live_child_root
end TripleDP.Transitions.Restriction
