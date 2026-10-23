import Work
open Universal233.CoreWork

def reviewEnvelope : Nat → Nat → Nat
  | 0,l => l+5
  | q+1,l => l+2*reviewEnvelope q l+9*2^(q+1)

theorem reviewEnvelope_closed (q l : Nat) :
    reviewEnvelope q l ≤ (l+6)*(q+1)*2^(q+1) := by
  induction q with
  | zero => simp only [reviewEnvelope]; omega
  | succ q ih =>
    let p := 2^(q+1)
    change reviewEnvelope q l ≤ (l+6)*(q+1)*p at ih
    have hp : 1 ≤ p := Nat.one_le_pow _ _ (by decide)
    have hl : l ≤ l*p := by simpa using Nat.mul_le_mul_left l hp
    have htail : l+9*p ≤ 2*((l+6)*p) := by
      simp only [Nat.add_mul] at *
      omega
    have expand : (l+6)*(q+1+1)*2^(q+1+1) =
        2*((l+6)*(q+1)*p)+2*((l+6)*p) := by
      simp only [p,Nat.pow_succ,Nat.mul_add,Nat.add_mul,Nat.mul_one]
      ac_rfl
    rw [expand]
    change l+2*reviewEnvelope q l+9*p ≤ _
    omega

theorem review_literal_charge : reviewEnvelope 0 10 = 15 := by decide
#print axioms reviewEnvelope_closed
#print axioms review_literal_charge
