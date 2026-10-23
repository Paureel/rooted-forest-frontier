import Primitive
open Universal233.CoreWork

-- A separate, conservative source-operation sheet. This does not replace
-- the frozen author code; it makes the review's primitive-unit allowance explicit.
def reviewSheet (s a b : Nat) : Nat :=
  (s+16)*s + (s+8)*s + (6*s+3) + ((12*s+16)*s+3) + (12*s+16) +
  2*((b+1)*(6*s+12)+(6*s+16)*s+16) + ((s+8)*s+12*(s+a+1)) + 64

theorem reviewSheet_le (s a b : Nat) (hs : 1 ≤ s) :
    reviewSheet s a b ≤ 256*(s+a+b+1)^3 := by
  let r := s+a+b+1
  have hr : 2 ≤ r := by dsimp [r]; omega
  have hs0 : s ≤ r := by dsimp [r]; omega
  have hb : b+1 ≤ r := by dsimp [r]; omega
  have hsa : s+a+1 ≤ r := by dsimp [r]; omega
  have rr : r ≤ r*r := by simpa using Nat.mul_le_mul_left r (by omega : 1 ≤ r)
  have rrr : 2*(r*r) ≤ r*r*r := by
    have h := Nat.mul_le_mul_left (r*r) hr
    simpa only [Nat.mul_comm 2] using h
  have h1 := Nat.mul_le_mul (by omega : s+16 ≤ 17*r) hs0
  have h2 := Nat.mul_le_mul (by omega : s+8 ≤ 9*r) hs0
  have h3 := Nat.mul_le_mul (by omega : 12*s+16 ≤ 28*r) hs0
  have h4 := Nat.mul_le_mul hb (by omega : 6*s+12 ≤ 18*r)
  have h5 := Nat.mul_le_mul (by omega : 6*s+16 ≤ 22*r) hs0
  have h6 : 1 ≤ r*r := by omega
  simp only [Nat.mul_assoc] at h1 h2 h3 h4 h5
  have hsheet : reviewSheet s a b ≤ 391*(r*r) := by
    unfold reviewSheet
    omega
  change reviewSheet s a b ≤ 256*r^3
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
  omega
#print axioms reviewSheet_le
