import Std

/- Conditional ownership implications only. They do not prove graph spans,
   source-core generation, exact rooted MAF, or a universal smaller exponent.
   Hypotheses explicitly identify the missing consumer interfaces. -/
namespace JointMacro

theorem threeOwnerCover
    (cross0 cross1 cross2 good0 good1 good2 : Prop)
    (h01 : ¬ (cross0 ∧ cross1))
    (h02 : ¬ (cross0 ∧ cross2))
    (h12 : ¬ (cross1 ∧ cross2))
    (core0 : ¬ cross0 → good0)
    (core1 : ¬ cross1 → good1)
    (core2 : ¬ cross2 → good2) :
    (good1 ∧ good2) ∨ (good0 ∧ good2) ∨ (good0 ∧ good1) := by
  classical
  by_cases p0 : cross0
  · exact Or.inl ⟨core1 (fun p1 => h01 ⟨p0, p1⟩),
      core2 (fun p2 => h02 ⟨p0, p2⟩)⟩
  · by_cases p1 : cross1
    · exact Or.inr (Or.inl ⟨core0 p0, core2 (fun p2 => h12 ⟨p1, p2⟩)⟩)
    · exact Or.inr (Or.inr ⟨core0 p0, core1 p1⟩)

/- An overlap chain has two independent edge ownership alternatives. No
   exchange deleting cross assignments is smuggled into this implication. -/
theorem chainFourCover (a b c d : Prop)
    (first : a ∨ b) (second : c ∨ d) :
    (a ∧ c) ∨ (a ∧ d) ∨ (b ∧ c) ∨ (b ∧ d) := by
  cases first with
  | inl ha =>
    cases second with
    | inl hc => exact Or.inl ⟨ha,hc⟩
    | inr hd => exact Or.inr (Or.inl ⟨ha,hd⟩)
  | inr hb =>
    cases second with
    | inl hc => exact Or.inr (Or.inr (Or.inl ⟨hb,hc⟩))
    | inr hd => exact Or.inr (Or.inr (Or.inr ⟨hb,hd⟩))

theorem independentCost (a b p q : Nat)
    (leftCost : a = p) (rightCost : b = q) : a + b = p + q := by
  rw [leftCost, rightCost]

/- Cleared positive denominators for the complete common-edge vector and
   the measured cheap chain edge pair. Kernel arithmetic; no native_decide. -/
theorem commonEdgeMass :
    2 * 100 * 231^3 + 3 * 100^4 < 231^4 := by decide

theorem measuredChainMass :
    2 * 100 * 231^4 + 2 * 100^4 * 231 + 4 * 100^5 < 231^5 := by decide

theorem uniformFourChainFails :
    231^4 < 2 * 100 * 231^3 + 4 * 100^4 := by decide

#print axioms threeOwnerCover
#print axioms chainFourCover
#print axioms independentCost
#print axioms commonEdgeMass
#print axioms measuredChainMass
#print axioms uniformFourChainFails
end JointMacro
