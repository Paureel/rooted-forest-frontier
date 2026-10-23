import ChargeConsumer

namespace TripleDP.RestrictionCharge.Sentinel
open TripleDP.CostRoute

/-- Every index is this single element; an actual leaf family. -/
def singletonLeaf {J : Type} (j : J) (only : ∀ k, k = j) : Family (.leaf (7 : Nat)) J where
  finite := ⟨[j], by simp, by intro k; simp [only k]⟩
  support := fun _ a => a = []
  bounded := by intro _ _ h; exact h
  convex := by
    intro _ a b ha hb v hv
    subst a; subst b
    rcases hv.2 with h | h <;> exact List.prefix_nil.mp h
  labelled := by intro _; exact ⟨[], 7, ⟨rfl, rfl⟩, rfl⟩
  disjoint := by intro i k _ _ _; exact (only i).trans (only k).symm
  covers := by intro a _ h; exact ⟨j, h.1⟩
  boundary := some j
  root_spec := by intro i; simp [only i]

def unitLeaf := singletonLeaf () (fun k => by cases k; rfl)
def parent := closeBoth unitLeaf unitLeaf

def left : Sum Unit Unit → Bool
  | .inl _ => true
  | .inr _ => false

def right : Sum Unit Unit → Bool
  | .inl _ => false
  | .inr _ => true

def leftIndex : {i // left i = true} := ⟨.inl (), rfl⟩
def rightIndex : {i // right i = true} := ⟨.inr (), rfl⟩

def childLeft := singletonLeaf leftIndex (by
  intro k
  apply Subtype.ext
  rcases k with ⟨i, hi⟩
  cases i with
  | inl u => cases u; rfl
  | inr u => simp [left] at hi)

def childRight := singletonLeaf rightIndex (by
  intro k
  apply Subtype.ext
  rcases k with ⟨i, hi⟩
  cases i with
  | inl u => simp [right] at hi
  | inr u => cases u; rfl)

theorem consumerT1 :
    parent.cost = childLeft.cost + childRight.cost +
      boundaryCharge childLeft.boundary + boundaryCharge childRight.boundary := by
  apply (conditional_family_costs parent left right childLeft childRight
    (by rfl) (by rfl) ?_ ?_ ?_ ?_ ?_ ?_).1
  · rfl
  · intro j a
    rcases j with ⟨i, hi⟩
    cases i with
    | inl u => rfl
    | inr u => simp [left] at hi
  · intro j a
    rcases j with ⟨i, hi⟩
    cases i with
    | inl u => simp [right] at hi
    | inr u => rfl
  · intro i
    cases i <;> simp [left, right]
  · intro i hl hr
    cases i <;> simp [left, right] at hl hr
  · intro i hs
    cases i with
    | inl u => rfl
    | inr u => exact False.elim hs.1
  · intro i hs
    cases i with
    | inl u => exact False.elim (Bool.noConfusion hs.1)
    | inr u => rfl

example : parent.cost = 2 := by decide
example : childLeft.cost = 0 := by decide
example : childRight.cost = 0 := by decide
#print axioms consumerT1
end TripleDP.RestrictionCharge.Sentinel
