import OutsideExact
namespace OrdinaryCommonSplit.Caller
open RMAF

def callbackMass (c : Rat) (d : Setup) (q : Nat) : Rat :=
  ((paidJobs d q).map (fun j=>c^(-((q-j.budget : Nat) : Int)))).sum

theorem callback_mass_eq (c : Rat) (d : Setup) (q : Nat) (positive : 0<q) :
    callbackMass c d q=2*c^(-1 : Int) := by
  have zero : q≠0 := by omega
  have drop : q-(q-1)=1 := by omega
  simp only [callbackMass,paidJobs,ite_eq_right zero,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,drop]
  grind

theorem callback_mass_bound (c : Rat) (hc : 2≤c) (d : Setup) (q : Nat) :
    callbackMass c d q≤1 := by
  by_cases zero : q=0
  · subst q
    simp [callbackMass,paidJobs]
    exact (by decide : (0 : Rat)≤1)
  · rw [callback_mass_eq c d q (by omega)]
    have cp : 0<c := by grind
    have cn := Rat.ne_of_gt cp
    have negone : c^(-1 : Int)=c⁻¹ := by rw [Rat.zpow_neg,Rat.zpow_one]
    rw [negone]
    apply Rat.le_of_mul_le_mul_right (c:=c) _ cp
    rw [Rat.mul_assoc,Rat.inv_mul_cancel c cn,Rat.mul_one,Rat.one_mul]
    exact hc

theorem target_mass : (2 : Rat)*(233/100 : Rat)^(-1 : Int)=200/233 ∧
    (200/233 : Rat)<1 := by
  rw [Rat.zpow_neg,Rat.zpow_one]
  constructor <;> grind

theorem pair_map_count {α β γ : Type} (A : List α) (B : List β) (f : α→β→γ) :
    (A.flatMap fun a=>B.map (f a)).length=A.length*B.length := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_cons,ih]
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- Counts every generated candidate, including failed owner guesses and
duplicate values. This is a count only, not a fine-source work theorem. -/
theorem mergeCandidates_length (X Y : List Nat) (x y rho gamma : Nat) (FM FN : Forest) :
    (mergeCandidates X Y x y rho gamma FM FN).length=FM.length*FN.length := by
  unfold mergeCandidates
  rw [pair_map_count,relabelForest_length,relabelForest_length]
end OrdinaryCommonSplit.Caller
