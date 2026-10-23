-- Superseded exploration only: the Rat equality s*s=2 is vacuous.
-- No theorem in this file is used by the accepted route result.
import Std
example (s : Rat) (hs0 : 0 ≤ s) (hs2 : s*s = 2) :
    (9/4 : Rat) * (1+s) < (23391/10000 : Rat) * (23391/10000 : Rat) := by
  have hsBound : s < (142/100 : Rat) := by
    apply Rat.not_le.mp
    intro hn
    have h1 : (142/100 : Rat) * (142/100 : Rat) ≤ s * (142/100 : Rat) :=
      Rat.mul_le_mul_of_nonneg_right hn (by decide +kernel)
    have h2 : s * (142/100 : Rat) ≤ s*s :=
      Rat.mul_le_mul_of_nonneg_left hn hs0
    have h3 := Rat.le_trans h1 h2
    rw [hs2] at h3
    exact (by decide +kernel : ¬ ((142/100 : Rat)*(142/100 : Rat) ≤ 2)) h3
  have hsum : 1+s < (1+142/100 : Rat) := by grind
  have hprod := Rat.mul_lt_mul_of_pos_left hsum (by decide +kernel : (0 : Rat) < 9/4)
  have hfixed : (9/4 : Rat) * (1+142/100) < (23391/10000 : Rat) * (23391/10000 : Rat) := by decide +kernel
  grind
