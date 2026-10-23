import RestrictionGeometry

namespace TripleDP.Transitions.Restriction
open TripleDP.CostRoute

variable {α I : Type} {l r : BTree α}

noncomputable def childBoundary (A : Family (.node l r) I)
    (h : OpenBranchLive A) (side : Bool) : Option (LiveIndex A side) := by
  classical
  exact if he : ∃ i, A.support i [side] then
    some ⟨Classical.choose he,
      occupied_live A h (Classical.choose he) side ⟨[], Classical.choose_spec he⟩⟩
    else none

theorem childBoundary_spec (A : Family (.node l r) I)
    (h : OpenBranchLive A) (side : Bool) (i : LiveIndex A side) :
    A.support i.val [side] ↔ childBoundary A h side = some i := by
  classical
  unfold childBoundary
  split
  next he =>
    constructor
    · intro hi
      apply congrArg some
      apply Subtype.ext
      exact A.disjoint (Classical.choose he) i.val [side] (Classical.choose_spec he) hi
    · intro hi
      have eqv := congrArg Subtype.val (Option.some.inj hi)
      simpa only [eqv] using Classical.choose_spec he
  next he =>
    constructor
    · intro hi; exact False.elim (he ⟨i.val, hi⟩)
    · intro hi; cases hi

noncomputable def restrict (A : Family (.node l r) I)
    (h : OpenBranchLive A) (side : Bool) : Family (child l r side) (LiveIndex A side) := by
  classical
  exact {
    finite := selectIndex A.finite (Live A side)
    support := fun i a => A.support i.val (side :: a)
    bounded := by
      intro i a ha
      cases side <;> exact A.bounded i.val _ ha
    convex := fun i => pathConvex_child_restriction (A.support i.val) (A.convex i.val) side
    labelled := fun i => i.property
    disjoint := by
      intro i j a hi hj
      exact Subtype.ext (A.disjoint i.val j.val (side :: a) hi hj)
    covers := by
      intro a x hx
      have hx' : LeafAt (.node l r) (side :: a) x := by cases side <;> exact hx
      rcases A.covers (side :: a) x hx' with ⟨i, hi⟩
      exact ⟨⟨i, a, x, hx, hi⟩, hi⟩
    boundary := childBoundary A h side
    root_spec := childBoundary_spec A h side }

theorem restrict_support (A : Family (.node l r) I) (h : OpenBranchLive A)
    (side : Bool) (i : LiveIndex A side) :
    (restrict A h side).support i = fun a => A.support i.val (side :: a) := rfl

theorem restrict_boundary_iff (A : Family (.node l r) I) (h : OpenBranchLive A)
    (side : Bool) (i : LiveIndex A side) :
    (restrict A h side).boundary = some i ↔ A.support i.val [side] :=
  (childBoundary_spec A h side i).symm

theorem restrict_labels (A : Family (.node l r) I) (h : OpenBranchLive A)
    (side : Bool) (i : LiveIndex A side) (x : α) :
    (restrict A h side).hasLabel i x ↔
      ∃ a, LeafAt (child l r side) a x ∧ A.support i.val (side :: a) := Iff.rfl

noncomputable def liveIndices (A : Family (.node l r) I) (side : Bool) : List I := by
  classical
  exact A.finite.elems.filter (fun i => decide (Live A side i))

theorem restrict_count (A : Family (.node l r) I) (h : OpenBranchLive A)
    (side : Bool) : (restrict A h side).blockCount = (liveIndices A side).length := by
  classical
  exact selectIndex_length A.finite (Live A side)

theorem restrict_open_boundary (A : Family (.node l r) I) (h : OpenBranchLive A)
    (o : I) (ho : A.boundary = some o) (side : Bool) (hl : Live A side o) :
    (restrict A h side).boundary = some ⟨o, hl⟩ :=
  (restrict_boundary_iff A h side ⟨o, hl⟩).mpr (open_live_child_root A o ho side hl)

#print axioms childBoundary_spec
#print axioms restrict
#print axioms restrict_support
#print axioms restrict_boundary_iff
#print axioms restrict_labels
#print axioms restrict_count
#print axioms restrict_open_boundary
end TripleDP.Transitions.Restriction
