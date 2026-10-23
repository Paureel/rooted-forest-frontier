import ConsumerSentinel
namespace TripleDP.RestrictionCharge.ReviewerT1
open TripleDP.CostRoute TripleDP.RestrictionCharge.Sentinel

theorem actual_count_consumer : childLeft.blockCount + childRight.blockCount = parent.blockCount := by
  have h := conditional_family_count parent left right childLeft childRight
    (by rfl) (by rfl)
    (by intro i; cases i <;> simp [left, right])
    (by intro i hl hr; cases i <;> simp [left, right] at hl hr)
  simpa [parent, closeBoth, duplicate] using h

theorem exact_T1 :
    parent.blockCount = 2 ∧ parent.cost = 2 ∧
    childLeft.blockCount = 1 ∧ childLeft.cost = 0 ∧
    childRight.blockCount = 1 ∧ childRight.cost = 0 ∧
    boundaryCharge childLeft.boundary + boundaryCharge childRight.boundary = 2 := by decide

theorem distinct_parent_indices : (Sum.inl () : Sum Unit Unit) ≠ Sum.inr () := by decide

theorem left_support_exact (j : {i // left i = true}) (a : Address) :
    childLeft.support j a ↔ parent.support j.val (false :: a) := by
  rcases j with ⟨i, hi⟩
  cases i with
  | inl u => change (a = []) ↔ (false = false ∧ a = []); simp
  | inr u => simp [left] at hi

theorem right_support_exact (j : {i // right i = true}) (a : Address) :
    childRight.support j a ↔ parent.support j.val (true :: a) := by
  rcases j with ⟨i, hi⟩
  cases i with
  | inl u => simp [right] at hi
  | inr u => change (a = []) ↔ (true = true ∧ a = []); simp

#print axioms actual_count_consumer
#print axioms exact_T1
#print axioms distinct_parent_indices
#print axioms left_support_exact
#print axioms right_support_exact
end TripleDP.RestrictionCharge.ReviewerT1
