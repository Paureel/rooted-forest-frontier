import Primitive
open Universal233.CoreWork

def reviewWideSheet (s a b : Nat) : Nat :=
  (s+24)*s + (s+16)*s + (8*s+4) + ((16*s+24)*s+4) + (16*s+24) +
  2*((b+1)*(8*s+24)+(8*s+24)*s+32) + ((s+16)*s+24*(s+a+1)) + 96

theorem reviewWideSheet_coarse (s a b : Nat) :
    reviewWideSheet s a b ≤ 567*((s+a+b+1)*(s+a+b+1)) := by
  let r := s+a+b+1
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hs : s ≤ r := by dsimp [r]; omega
  have hb : b+1 ≤ r := by dsimp [r]; omega
  have hsa : s+a+1 ≤ r := by dsimp [r]; omega
  have rr : r ≤ r*r := by simpa using Nat.mul_le_mul_left r hr
  have rpos : 1 ≤ r*r := by omega
  have h1 := Nat.mul_le_mul (by omega : s+24 ≤ 25*r) hs
  have h2 := Nat.mul_le_mul (by omega : s+16 ≤ 17*r) hs
  have h3 := Nat.mul_le_mul (by omega : 16*s+24 ≤ 40*r) hs
  have h4 : (b+1)*(8*s+24) ≤ 32*(r*r) := by
    calc
      _ ≤ r*(32*r) := Nat.mul_le_mul hb (by omega)
      _ = _ := by ac_rfl
  have h5 := Nat.mul_le_mul (by omega : 8*s+24 ≤ 32*r) hs
  have h6 : 8*s+4 ≤ 12*(r*r) := by omega
  have h7 : 16*s+24 ≤ 40*(r*r) := by omega
  have h8 : 24*(s+a+1) ≤ 24*(r*r) := by omega
  simp only [Nat.mul_assoc] at h1 h2 h3 h5
  change reviewWideSheet s a b ≤ 567*(r*r)
  unfold reviewWideSheet
  omega

theorem reviewWideSheet_cap (s a b m : Nat) (h : s+a+b ≤ m) (hm : 2 ≤ m) :
    reviewWideSheet s a b ≤ cap m := by
  have hcoarse := reviewWideSheet_coarse s a b
  have hprod := Nat.mul_le_mul (by omega : s+a+b+1 ≤ m+1) (by omega : s+a+b+1 ≤ m+1)
  have hp : 1 ≤ (m+1)*(m+1) := by have hh := Nat.mul_le_mul (by omega : 1 ≤ m+1) (by omega : 1 ≤ m+1); omega
  have hcube := Nat.mul_le_mul_left ((m+1)*(m+1)) (by omega : 3 ≤ m+1)
  unfold cap
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
  omega

def reviewWideEnvelope : Nat → Nat → Nat
  | 0,l => l+10
  | q+1,l => l+2*reviewWideEnvelope q l+24*2^(q+1)

theorem reviewWideEnvelope_closed (q l : Nat) (hlow : 12 ≤ l) :
    reviewWideEnvelope q l ≤ (l+6)*(q+1)*2^(q+1) := by
  induction q with
  | zero => simp only [reviewWideEnvelope]; omega
  | succ q ih =>
    let p := 2^(q+1)
    change reviewWideEnvelope q l ≤ (l+6)*(q+1)*p at ih
    have hp : 1 ≤ p := Nat.one_le_pow _ _ (by decide)
    have hl : l ≤ l*p := by simpa using Nat.mul_le_mul_left l hp
    have hlp : 12*p ≤ l*p := Nat.mul_le_mul_right p hlow
    have htail : l+24*p ≤ 2*((l+6)*p) := by
      simp only [Nat.add_mul] at *
      omega
    have expand : (l+6)*(q+1+1)*2^(q+1+1) =
        2*((l+6)*(q+1)*p)+2*((l+6)*p) := by
      simp only [p,Nat.pow_succ,Nat.mul_add,Nat.add_mul,Nat.mul_one]
      ac_rfl
    rw [expand]
    change l+2*reviewWideEnvelope q l+24*p ≤ _
    omega

theorem reviewInitial (n : Nat) :
    22*(n*n)+80*n+16 ≤ 128*(n+1)^3 := by
  have hp : 1 ≤ n+1 := by omega
  have hh := Nat.mul_le_mul_left ((n+1)*(n+1)) hp
  have hs : 22*(n*n)+80*n+16 ≤ 128*((n+1)*(n+1)) := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    omega
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
  omega

#print axioms reviewWideSheet_cap
#print axioms reviewWideEnvelope_closed
#print axioms reviewInitial
