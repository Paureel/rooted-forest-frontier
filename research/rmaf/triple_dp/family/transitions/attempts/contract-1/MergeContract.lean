import FamilyMerge

namespace TripleDP.Transitions
open TripleDP.CostRoute

variable {α I J : Type} {l r : BTree α}

theorem merge_keeps_left [DecidableEq J] (f : Family l I) (g : Family r J)
    (o i : I) (p : J) (ho : f.boundary = some o) (hp : g.boundary = some p)
    (hi : i ≠ o) :
    (merge f g o p ho hp).support (.inl i) = liftSupport false (f.support i) := by
  funext a
  simp [merge, mergeSupport, hi]

theorem merge_keeps_right [DecidableEq J] (f : Family l I) (g : Family r J)
    (o : I) (p : J) (j : {j : J // j ≠ p})
    (ho : f.boundary = some o) (hp : g.boundary = some p) :
    (merge f g o p ho hp).support (.inr j) = liftSupport true (g.support j.val) := rfl

theorem merge_boundary_support [DecidableEq J] (f : Family l I) (g : Family r J)
    (o : I) (p : J) (ho : f.boundary = some o) (hp : g.boundary = some p) :
    (merge f g o p ho hp).support (.inl o) =
      (fun a => a = [] ∨ liftSupport false (f.support o) a ∨
        liftSupport true (g.support p) a) := by
  funext a
  simp [merge, mergeSupport, or_comm, or_left_comm]

theorem merge_labels_left [DecidableEq J] (f : Family l I) (g : Family r J)
    (o i : I) (p : J) (ho : f.boundary = some o) (hp : g.boundary = some p)
    (hi : i ≠ o) (x : α) :
    (merge f g o p ho hp).hasLabel (.inl i) x ↔ f.hasLabel i x := by
  unfold Family.hasLabel
  rw [merge_keeps_left f g o i p ho hp hi]
  exact closeBoth_hasLabel_left f g i x

theorem merge_labels_right [DecidableEq J] (f : Family l I) (g : Family r J)
    (o : I) (p : J) (j : {j : J // j ≠ p})
    (ho : f.boundary = some o) (hp : g.boundary = some p) (x : α) :
    (merge f g o p ho hp).hasLabel (.inr j) x ↔ g.hasLabel j.val x := by
  unfold Family.hasLabel
  rw [merge_keeps_right f g o p j ho hp]
  exact closeBoth_hasLabel_right f g j.val x

theorem merge_labels_boundary [DecidableEq J] (f : Family l I) (g : Family r J)
    (o : I) (p : J) (ho : f.boundary = some o) (hp : g.boundary = some p) (x : α) :
    (merge f g o p ho hp).hasLabel (.inl o) x ↔ f.hasLabel o x ∨ g.hasLabel p x := by
  constructor
  · rintro ⟨a, hx, ha⟩
    cases a with
    | nil => exact False.elim hx
    | cons side a =>
      cases side with
      | false => exact Or.inl ⟨a, hx, by simpa [merge] using ha⟩
      | true => exact Or.inr ⟨a, hx, by simpa [merge] using ha⟩
  · rintro (⟨a, hx, ha⟩ | ⟨a, hx, ha⟩)
    · exact ⟨false :: a, hx, by simpa [merge] using ha⟩
    · exact ⟨true :: a, hx, by simpa [merge] using ha⟩

/-- Universal existence without a decidable-equality premise in the statement.
The witness exports exact support equations as well as count and cost. -/
theorem merge_universal (f : Family l I) (g : Family r J) (o : I) (p : J)
    (ho : f.boundary = some o) (hp : g.boundary = some p) :
    ∃ A : Family (.node l r) (MergeIndex I p),
      A.boundary = some (.inl o) ∧
      (∀ i, i ≠ o → A.support (.inl i) = liftSupport false (f.support i)) ∧
      (∀ j : {j : J // j ≠ p}, A.support (.inr j) = liftSupport true (g.support j.val)) ∧
      A.support (.inl o) = (fun a => a = [] ∨ liftSupport false (f.support o) a ∨
        liftSupport true (g.support p) a) ∧
      A.blockCount = f.blockCount + g.blockCount - 1 ∧ A.cost = f.cost + g.cost := by
  classical
  refine ⟨merge f g o p ho hp, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; exact merge_keeps_left f g o i p ho hp hi
  · intro j; exact merge_keeps_right f g o p j ho hp
  · exact merge_boundary_support f g o p ho hp
  · exact merge_count f g o p ho hp
  · exact merge_cost f g o p ho hp

#print axioms merge_keeps_left
#print axioms merge_keeps_right
#print axioms merge_boundary_support
#print axioms merge_labels_left
#print axioms merge_labels_right
#print axioms merge_labels_boundary
#print axioms merge_universal
end TripleDP.Transitions
