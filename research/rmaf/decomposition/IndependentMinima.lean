import Std

/-
Generic certificate gluing lemma. This proves a Cartesian-product cost fact,
not the assertion that a rooted-MAF split satisfies the Cartesian-product
hypothesis. That structural identification remains an explicit missing lemma.
-/
namespace RMAF.Decomposition

theorem independent_minima
    {A B : Type} (allowedA : A → Prop) (allowedB : B → Prop)
    (costA : A → Nat) (costB : B → Nat) (a b : Nat)
    (lowerA : ∀ x, allowedA x → a ≤ costA x)
    (lowerB : ∀ y, allowedB y → b ≤ costB y)
    (attainA : ∃ x, allowedA x ∧ costA x = a)
    (attainB : ∃ y, allowedB y ∧ costB y = b) :
    (∃ x y, allowedA x ∧ allowedB y ∧ costA x + costB y = a + b) ∧
    (∀ x y, allowedA x → allowedB y → a + b ≤ costA x + costB y) := by
  constructor
  · rcases attainA with ⟨x, hx, hcostx⟩
    rcases attainB with ⟨y, hy, hcosty⟩
    refine ⟨x, y, hx, hy, ?_⟩
    simp [hcostx, hcosty]
  · intro x y hx hy
    exact Nat.add_le_add (lowerA x hx) (lowerB y hy)

#print axioms independent_minima
end RMAF.Decomposition

namespace RMAF.Decomposition
/- Counting consequence only. It does not prove any MAF chain reduction safe,
nor establish a new kernel; generator-side hypotheses are external obligations. -/
theorem hypothetical_two_leaf_side_count (k0 k1 : Nat)
    (positive : 1 ≤ k0 + k1) :
    2 * k0 + 2 * (2 * k0 + 3 * k1 - 1) + k0 ≤
      7 * (k0 + k1) - 2 := by
  omega

#print axioms hypothetical_two_leaf_side_count
end RMAF.Decomposition
