import SupportProfile
namespace RestrictionRoute
open RMAF

theorem rootedSpan_isEmpty_node (A : List Nat) (l r : Tree) :
    (rootedSpan A (.node l r)).isEmpty =
      ((rootedSpan A l).isEmpty && (rootedSpan A r).isEmpty) := by
  cases hl : (rootedSpan A l).isEmpty <;> cases hr : (rootedSpan A r).isEmpty <;>
    simp [rootedSpan, hl, hr]

theorem rootedSpan_isEmpty_restrict_isNone (A : List Nat) (t : Tree) :
    (rootedSpan A t).isEmpty = (restrict A t).isNone := by
  induction t with
  | leaf x => simp only [rootedSpan, restrict]; split <;> rfl
  | node l r hl hr =>
      rw [rootedSpan_isEmpty_node, hl, hr, restrict_node]
      cases restrict A l <;> cases restrict A r <;> rfl

theorem rootedSpan_eq_nil_iff_restrict_none (A : List Nat) (t : Tree) :
    rootedSpan A t = [] ↔ restrict A t = none := by
  rw [← List.isEmpty_iff, rootedSpan_isEmpty_restrict_isNone]
  cases restrict A t <;> simp

/-- An unselected subtree contributes no actual vertices for either subblock. -/
theorem supportProfile_empty_of_restrict_none (t : Tree) (A C B : List Nat)
    (hAB : ∀ x ∈ A, x ∈ B) (hCB : ∀ x ∈ C, x ∈ B)
    (hB : restrict B t = none) : supportProfile A C t = emptyProfile := by
  apply supportProfile_empty
  · apply (rootedSpan_eq_nil_iff_restrict_none A t).mpr
    have ha := restrict_associative_subset t A B hAB
    simpa [hB] using ha.symm
  · apply (rootedSpan_eq_nil_iff_restrict_none C t).mpr
    have hc := restrict_associative_subset t C B hCB
    simpa [hB] using hc.symm

/-- The exact support-intersection summary survives selection and suppression.
The proof follows the actual executable restriction, including both unary cases. -/
theorem supportProfile_restrict (t s : Tree) (A C B : List Nat)
    (hAB : ∀ x ∈ A, x ∈ B) (hCB : ∀ x ∈ C, x ∈ B)
    (hs : restrict B t = some s) : supportProfile A C t = supportProfile A C s := by
  induction t generalizing s with
  | leaf x =>
      simp only [restrict] at hs
      split at hs
      · cases hs; rfl
      · contradiction
  | node l r ihl ihr =>
      rw [restrict_node] at hs
      cases hl : restrict B l with
      | none =>
          cases hr : restrict B r with
          | none => simp [hl, hr, joinRestricted] at hs
          | some sr =>
              have heq : sr = s := by simpa [hl, hr, joinRestricted] using hs
              subst s
              rw [supportProfile_node, supportProfile_empty_of_restrict_none l A C B hAB hCB hl,
                joinProfile_empty]
              exact ihr sr hr
      | some sl =>
          cases hr : restrict B r with
          | none =>
              have heq : sl = s := by simpa [hl, hr, joinRestricted] using hs
              subst s
              rw [supportProfile_node, supportProfile_empty_of_restrict_none r A C B hAB hCB hr,
                joinProfile_comm, joinProfile_empty]
              exact ihl sl hl
          | some sr =>
              have heq : Tree.node sl sr = s := by simpa [hl, hr, joinRestricted] using hs
              subst s
              rw [supportProfile_node, supportProfile_node, ihl sl hl, ihr sr hr]

/-- Swapping children changes addresses but leaves all three intersection tests invariant. -/
theorem supportProfile_rootedIso {t u : Tree} (h : RootedIso t u) (A C : List Nat) :
    supportProfile A C t = supportProfile A C u := by
  induction h with
  | leaf x => rfl
  | straight h₁ h₂ ih₁ ih₂ =>
      rw [supportProfile_node, supportProfile_node, ih₁, ih₂]
  | swapped h₁ h₂ ih₁ ih₂ =>
      rw [supportProfile_node, supportProfile_node, ih₁, ih₂, joinProfile_comm]

/-- Exact actual-support disjointness transport through an agreeing restriction.
Only subset membership is needed: uniqueness, two-block coverage and equal full
leaf sets are unnecessary for this transport statement. -/
theorem actual_disjoint_transport_eq (t u : Tree) (A C B : List Nat)
    (hAB : ∀ x ∈ A, x ∈ B) (hCB : ∀ x ∈ C, x ∈ B)
    (hB : restrictionAgrees t u B = true) :
    disjointVertices (minimalVertices A t) (minimalVertices C t) =
      disjointVertices (minimalVertices A u) (minimalVertices C u) := by
  cases ht : restrict B t with
  | none => simp [restrictionAgrees, ht] at hB
  | some tb =>
      cases hu : restrict B u with
      | none => simp [restrictionAgrees, hu] at hB
      | some ub =>
          have hiso : RootedIso tb ub := (sameShape_correct tb ub).mp (by
            simpa [restrictionAgrees, ht, hu] using hB)
          have heq : supportProfile A C t = supportProfile A C u :=
            (supportProfile_restrict t tb A C B hAB hCB ht).trans
              ((supportProfile_rootedIso hiso A C).trans
                (supportProfile_restrict u ub A C B hAB hCB hu).symm)
          exact congrArg PairProfile.minMin heq

theorem actual_disjoint_transport (t u : Tree) (A C B : List Nat)
    (hAB : ∀ x ∈ A, x ∈ B) (hCB : ∀ x ∈ C, x ∈ B)
    (hB : restrictionAgrees t u B = true)
    (hApart : disjointVertices (minimalVertices A t) (minimalVertices C t) = true) :
    disjointVertices (minimalVertices A u) (minimalVertices C u) = true := by
  rw [← actual_disjoint_transport_eq t u A C B hAB hCB hB]
  exact hApart

/-- The exact outputs needed by the parent's refinement consumer: two hereditary
agreement facts and target-tree disjointness, from the source-tree disjointness. -/
theorem two_block_transport (t u : Tree) (A C B : List Nat)
    (hAB : ∀ x ∈ A, x ∈ B) (hCB : ∀ x ∈ C, x ∈ B)
    (hBt : ∀ x ∈ B, x ∈ leaves t) (hA : A ≠ []) (hC : C ≠ [])
    (hB : restrictionAgrees t u B = true)
    (hApart : disjointVertices (minimalVertices A t) (minimalVertices C t) = true) :
    restrictionAgrees t u A = true ∧ restrictionAgrees t u C = true ∧
    disjointVertices (minimalVertices A u) (minimalVertices C u) = true := by
  exact ⟨restrictionAgrees_subset t u A B hAB (fun x hx => hBt x (hAB x hx)) hA hB,
    restrictionAgrees_subset t u C B hCB (fun x hx => hBt x (hCB x hx)) hC hB,
    actual_disjoint_transport t u A C B hAB hCB hB hApart⟩

#print axioms two_block_transport

#print axioms supportProfile_restrict
#print axioms supportProfile_rootedIso
#print axioms actual_disjoint_transport_eq
#print axioms actual_disjoint_transport
end RestrictionRoute
