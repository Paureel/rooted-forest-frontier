import Std

namespace ThesisCredit

/-- Normalize every coefficient by 16 for p=1 and a three-pendant G4 A3BC. -/
def parent16 (q : Nat) : Nat := 8 + 4*q
def children16 (q : Nat) : Nat := (4 + 2*q) + 2 + (3+q)

theorem g4_credit_condition (q : Nat) :
    children16 q ≤ parent16 q ↔ 1 ≤ q := by
  unfold children16 parent16
  omega

theorem g4_q_zero_fails : ¬ children16 0 ≤ parent16 0 := by decide
theorem g4_q_one_passes : children16 1 = parent16 1 := by decide

/-- x=alpha*2^k/16; include every p-3 offset and the current invocation. -/
def parentBound (x : Int) : Int := 8*x-2
def composedBound (x : Int) : Int := 1 + (4*x-2) + (2*x-3) + (3*x-1)

theorem affine_gap (x : Int) : composedBound x - parentBound x = x-3 := by
  unfold composedBound parentBound
  omega

theorem affine_failure (x : Int) (hx : 4 ≤ x) : parentBound x < composedBound x := by
  unfold composedBound parentBound
  omega

theorem exact_affine_witness : parentBound 4 = 30 ∧ composedBound 4 = 31 := by decide

/-- Source G1's normalized A2BC and A3BC sums. -/
theorem g1_A2 : 8 + 4 + 4 = (16:Nat) := by decide
theorem g1_A3 : 8 + 2 + 6 = (16:Nat) := by decide

/-- A count-only union lift can leave the claimed |P|≤2 state space. -/
theorem triple_credit_violates_cap : ¬ (3:Nat) ≤ 2 := by decide

/-- A possible repair for the arithmetic: strengthen C-child weight 3/8 to 1/4.
This theorem supplies no structural justification for that stronger bound. -/
theorem conditional_repair : 4 + 2 + 2 = (8:Nat) := by decide

#print axioms g4_credit_condition
#print axioms g4_q_zero_fails
#print axioms g4_q_one_passes
#print axioms affine_gap
#print axioms affine_failure
#print axioms exact_affine_witness
#print axioms g1_A2
#print axioms g1_A3
#print axioms triple_credit_violates_cap
#print axioms conditional_repair
end ThesisCredit
