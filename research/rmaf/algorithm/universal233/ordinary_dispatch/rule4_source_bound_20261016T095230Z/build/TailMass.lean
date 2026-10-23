import MinimumUnique

/-! Literal raw-output-LIST tail bound. The domain premise is discharged by
`generate_rawQ_mass` at base two, not postulated for an abstract cost multiset. -/
namespace Universal233.RankDichotomy
open RMAF CoreProgram SourceCoverage

theorem inv_le_half (b : Rat) (hb : 2 ≤ b) : b⁻¹ ≤ (2 : Rat)⁻¹ := by
  have hbpos : 0 < b := by grind
  apply Rat.le_of_mul_le_mul_right (c := b) _ hbpos
  rw [Rat.inv_mul_cancel b (Rat.ne_of_gt hbpos)]
  have hm := Rat.mul_le_mul_of_nonneg_left hb
    (Rat.le_of_lt (Rat.inv_pos.mpr (by decide : 0 < (2 : Rat))))
  rw [Rat.inv_mul_cancel (2 : Rat) (by decide)] at hm
  exact hm

theorem negpow_succ (b : Rat) (hb : b ≠ 0) (n : Nat) :
    b ^ (-((n+1 : Nat) : Int)) = b ^ (-(n : Int)) * b⁻¹ := by
  have he : -((n+1 : Nat) : Int) = -(n : Int) + (-1 : Int) := by omega
  have hone : b ^ (-1 : Int) = b⁻¹ := by rw [Rat.zpow_neg b 1,Rat.zpow_one]
  rw [he,Rat.zpow_add hb,hone]

theorem tail_term (b : Rat) (hb : 2 ≤ b) (L d : Nat) (hd : L ≤ d) :
    b ^ (-(d : Int)) ≤ ((2 : Rat)^L * b^(-(L : Int))) * (2 : Rat)^(-(d : Int)) := by
  have hbpos : 0 < b := by grind
  have hbne : b ≠ 0 := Rat.ne_of_gt hbpos
  have hipos := Rat.inv_pos.mpr hbpos
  have hhalf := inv_le_half b hb
  let K : Rat := (2 : Rat)^L * b^(-(L : Int))
  have hK : 0 < K := Rat.mul_pos (Rat.pow_pos (by decide)) (Rat.zpow_pos hbpos)
  change b ^ (-(d : Int)) ≤ K * (2 : Rat)^(-(d : Int))
  induction hd with
  | refl =>
      have hcancel : (2 : Rat)^L * (2 : Rat)^(-(L : Int)) = 1 := by
        rw [Rat.zpow_neg,Rat.zpow_natCast,Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.pow_pos (by decide)))]
      dsimp [K]
      have heq : ((2 : Rat)^L * b^(-(L : Int))) * (2 : Rat)^(-(L : Int)) = b^(-(L : Int)) := by
        rw [Rat.mul_assoc,Rat.mul_comm (b^(-(L : Int))) _,←Rat.mul_assoc,hcancel,Rat.one_mul]
      rw [heq]
      exact Rat.le_refl
  | @step d hd ih =>
      rw [negpow_succ b hbne,negpow_succ 2 (by decide)]
      have hfirst := Rat.mul_le_mul_of_nonneg_right ih (Rat.le_of_lt hipos)
      have hsecond := Rat.mul_le_mul_of_nonneg_left hhalf
        (Rat.le_of_lt (Rat.mul_pos hK (Rat.zpow_pos (a := (2 : Rat)) (n := -(d : Int)) (by decide))))
      exact Rat.le_trans hfirst (by simpa only [Rat.mul_assoc] using hsecond)

theorem rawQMass_tail (b : Rat) (hb : 2 ≤ b) (L : Nat) (xs : List Output)
    (hmin : ∀ o, o ∈ xs → L ≤ o.sourceCuts.length) :
    rawQMass b xs ≤ ((2 : Rat)^L * b^(-(L : Int))) * rawQMass 2 xs := by
  induction xs with
  | nil => simp [rawQMass]
  | cons o os ih =>
      have ht := tail_term b hb L o.sourceCuts.length (hmin o (by simp))
      have hs := ih (by intro a ha; exact hmin a (List.mem_cons_of_mem o ha))
      have hh := qadd_le_add ht hs
      simpa only [rawQMass,List.map_cons,List.sum_cons,Rat.mul_add] using hh

/-- Actual frozen generator + actual dyadic raw-list theorem + actual costs. -/
theorem generate_tail_mass (T : Tree) (color : Nat → Nat) (q L : Nat)
    (b : Rat) (hb : 2 ≤ b) (hL : inputRank T color - 1 ≤ L)
    (hmin : ∀ o, o ∈ (generate T color q).outputs → L ≤ o.sourceCuts.length) :
    rawQMass b (generate T color q).outputs ≤
      (2 : Rat)^(L - (inputRank T color - 1)) * b^(-(L : Int)) := by
  have hr := inputRank_pos T color
  have hbpos : 0 < b := by grind
  have ht := rawQMass_tail b hb L (generate T color q).outputs hmin
  have hd := generate_rawQ_mass T color q 2 (by decide)
  have he : 1 - (inputRank T color : Int) = -((inputRank T color - 1 : Nat) : Int) := by omega
  change rawQMass 2 (generate T color q).outputs ≤ (2 : Rat)^(1 - (inputRank T color : Int)) at hd
  rw [he] at hd
  have hK : 0 ≤ (2 : Rat)^L * b^(-(L : Int)) :=
    Rat.le_of_lt (Rat.mul_pos (Rat.pow_pos (a := (2 : Rat)) (n := L) (by decide))
      (Rat.zpow_pos (a := b) (n := -(L : Int)) hbpos))
  have hm := Rat.mul_le_mul_of_nonneg_left hd hK
  have hc := qpow_clear 2 (by decide) L (inputRank T color - 1) hL
  have hbound := Rat.le_trans ht hm
  calc
    _ ≤ ((2 : Rat)^L * b^(-(L : Int))) * (2 : Rat)^(-((inputRank T color - 1 : Nat) : Int)) := hbound
    _ = (2 : Rat)^(L - (inputRank T color - 1)) * b^(-(L : Int)) := by
      rw [hc,Rat.mul_assoc,Rat.mul_comm (b^(-(L : Int))) _,←Rat.mul_assoc]

theorem infeasible_mass (T : Tree) (color : Nat → Nat) (q : Nat)
    (hf : ¬RankFeasible T color) (b : Rat) (hb : 2 ≤ b) :
    rawQMass b (generate T color q).outputs ≤ 2 * b^(-(inputRank T color : Int)) := by
  have hr := inputRank_pos T color
  have hh := generate_tail_mass T color q (inputRank T color) b hb (by omega)
    (infeasible_cost T color q hf)
  have hd : inputRank T color - (inputRank T color - 1) = 1 := by omega
  simpa only [hd,Rat.pow_one] using hh

end Universal233.RankDichotomy
