import Std

/- Pure exact arithmetic; this file does not encode source tree geometry or reachability. -/
namespace RepairAdversary

/-- The rational coefficients multiplied by their positive common denominator 16. -/
theorem denominator_positive : (0 : Int) < 16 := by decide
theorem printed_mass_scaled : (4 : Int) + 2 + 3 = 9 := by decide
theorem printed_excess_scaled : (9 : Int) - 8 = 1 := by decide
theorem repaired_mass_scaled : (4 : Int) + 2 + 2 = 8 := by decide

/-- Clearing denominators gives a universal integer affine implication. -/
theorem joint_scaled (D M A B C : Int)
    (hA : D*A ≤ 4*M - 2*D) (hB : D*B ≤ 2*M - 3*D)
    (hC : D*C ≤ 2*M - D) :
    D*(1+A+B+C) ≤ 8*M - 5*D := by
  simp only [Int.mul_add, Int.mul_one]
  omega

theorem joint_scaled_target (D M A B C : Int) (hD : 0 ≤ D)
    (hA : D*A ≤ 4*M - 2*D) (hB : D*B ≤ 2*M - 3*D)
    (hC : D*C ≤ 2*M - D) :
    D*(1+A+B+C) ≤ 8*M - 2*D := by
  have h := joint_scaled D M A B C hA hB hC
  omega

/-- Source geometry must separately establish the two heights and their sum. -/
theorem deeper_height (hx hy : Nat) (sum : hx + hy = 5)
    (ordered : hy ≤ hx) : 3 ≤ hx := by omega

theorem surviving_height_child (hx hy : Nat) (sum : hx + hy = 5)
    (child : hy = 1) : 3 ≤ hx - 1 := by omega

theorem surviving_height_other (hx hy : Nat) (sum : hx + hy = 5)
    (ordered : hy ≤ hx) (notChild : 2 ≤ hy) : 3 ≤ hx := by omega

/-- K is the J budget; C spends one before its sole branch spends at least three. -/
theorem budget_drop (K s : Int) (hs : 3 ≤ s) : K - 1 - s ≤ K - 4 := by omega

theorem exact_slack (M : Int) :
    1 + (4*M - 2) + (2*M - 3) + (2*M - 1) = 8*M - 5 := by omega

end RepairAdversary
