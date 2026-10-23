import QueryBudgets

namespace Universal233.PaidQueries

theorem natural_count_step (p : Nat) (hp : 2 ≤ p) : p+1 ≤ 4*p := by omega
theorem natural_exponent_step (p : Nat) (hp : 2 ≤ p) :
    2*(p+1-1)-1 = (2*(p-1)-1)+1+1 := by omega

theorem count_power (c : Rat) (hc : 2 ≤ c) (p : Nat) (hp : 2 ≤ p) :
    (p : Rat) ≤ c ^ (2*(p-1)-1) := by
  induction hp with
  | refl => simpa [Rat.pow_one] using hc
  | @step p hp ih =>
    have cp : 0 ≤ (p : Rat) := Rat.natCast_nonneg
    have cc : 0 ≤ c := by grind
    have h4 : (4 : Rat) ≤ c*c := by
      have h1 := Rat.mul_le_mul_of_nonneg_right hc (by decide : 0 ≤ (2 : Rat))
      have h2 := Rat.mul_le_mul_of_nonneg_left hc cc
      have h22 : (2 : Rat)*2=4 := by grind
      rw [h22] at h1
      exact Rat.le_trans h1 h2
    have hn : (p+1 : Nat) ≤ 4*p := natural_count_step p hp
    have hcast : ((p+1 : Nat) : Rat) ≤ (p : Rat)*4 := by
      have h := Rat.natCast_le_natCast.2 hn
      simpa [Rat.natCast_mul,Rat.mul_comm] using h
    have hm := Rat.mul_le_mul_of_nonneg_left h4 cp
    have hi := Rat.mul_le_mul_of_nonneg_right ih
      (Rat.le_of_lt (Rat.mul_pos (by grind : 0<c) (by grind : 0<c)))
    have he : 2*(p+1-1)-1 = (2*(p-1)-1)+1+1 := natural_exponent_step p hp
    rw [he,Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans hcast (Rat.le_trans hm (by simpa [Rat.mul_assoc] using hi))

/-- At least two hard calls, each paid by all OTHER hard lower bounds, consume
    at most one c^-1 unit for every rational base at least2. -/
theorem multi_hard_mass (c : Rat) (hc : 2 ≤ c) (p : Nat) (hp : 2 ≤ p) :
    (p : Rat) * c^(-((2*(p-1) : Nat) : Int)) ≤ c^(-1 : Int) := by
  have cp : 0<c := by grind
  have cn := Rat.ne_of_gt cp
  have hh := count_power c hc p hp
  have hm := Rat.mul_le_mul_of_nonneg_right hh
    (Rat.le_of_lt (Rat.zpow_pos (a:=c) (n:= -((2*(p-1) : Nat) : Int)) cp))
  have he : (((2*(p-1)-1 : Nat) : Int) + -((2*(p-1) : Nat) : Int)) = -1 := by omega
  have hi : c^(2*(p-1)-1) * c^(-((2*(p-1) : Nat) : Int)) = c^(-1 : Int) := by
    rw [←Rat.zpow_natCast,←Rat.zpow_add cn,he]
  simpa only [hi] using hm

def queryEnvelope (c : Rat) (js : List (Job P A)) : Rat :=
  (pending js : Rat) * c^(-((knownCost js + 2*(pending js-1) : Nat) : Int))

theorem negpow_antitone (c : Rat) (hc : 2 ≤ c) (a b : Nat) (hab : a ≤ b) :
    c^(-(b : Int)) ≤ c^(-(a : Int)) := by
  have cp : 0<c := by grind
  have cn := Rat.ne_of_gt cp
  have hinv : c⁻¹ ≤ 1 := by
    apply Rat.le_of_mul_le_mul_right (c:=c) _ cp
    rw [Rat.inv_mul_cancel c cn,Rat.one_mul]
    grind
  induction hab with
  | refl => exact Rat.le_refl
  | @step b hab ih =>
    have he : -((b+1 : Nat) : Int) = -(b : Int)+(-1) := by omega
    have h1 : c^(-1 : Int) = c⁻¹ := by rw [Rat.zpow_neg,Rat.zpow_one]
    rw [he,Rat.zpow_add cn,h1]
    have hm := Rat.mul_le_mul_of_nonneg_left hinv
      (Rat.le_of_lt (Rat.zpow_pos (a:=c) (n:= -(b : Int)) cp))
    exact Rat.le_trans (by simpa [Rat.mul_one] using hm) ih

theorem paid_query_envelope (c : Rat) (hc : 2 ≤ c)
    (js : List (Job P A)) (hbad : 2 ≤ badSlots js) :
    queryEnvelope c js ≤ c^(-1 : Int) := by
  have hb := bad_le_known_pending js
  cases he : pending js with
  | zero => simp [queryEnvelope,he,Rat.zero_mul,Rat.le_of_lt (Rat.zpow_pos (a:=c) (n:=(-1 : Int)) (by grind : 0<c))]
  | succ p =>
    cases p with
    | zero =>
      have hk : 1 ≤ knownCost js := by omega
      have hm := negpow_antitone c hc 1 (knownCost js) hk
      simpa [queryEnvelope,he,Rat.one_mul] using hm
    | succ p =>
      have hp : 2 ≤ pending js := by omega
      have hm := multi_hard_mass c hc (pending js) hp
      have hmono := negpow_antitone c hc (2*(pending js-1))
        (knownCost js+2*(pending js-1)) (by omega)
      have hmul := Rat.mul_le_mul_of_nonneg_left hmono (show 0 ≤ (pending js : Rat) from Rat.natCast_nonneg)
      exact Rat.le_trans hmul hm

def actualQueryMass (c : Rat) (q : Nat) (calls : List Nat) : Rat :=
  (calls.map (fun b => c^(-((q-b : Nat) : Int)))).sum

theorem uniform_query_mass (c : Rat) (q b : Nat) (calls : List Nat)
    (h : ∀ k ∈ calls, k=b) :
    actualQueryMass c q calls = (calls.length : Rat)*c^(-((q-b : Nat) : Int)) := by
  induction calls with
  | nil => simp [actualQueryMass,Rat.zero_mul]
  | cons k ks ih =>
    have hk := h k (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [actualQueryMass,List.map_cons,List.sum_cons,List.length_cons] at *
    rw [hk,ht]
    have hn : ((ks.length+1 : Nat) : Rat) = (ks.length : Rat)+1 := by
      simp only [Rat.natCast_add,Rat.natCast_ofNat]
    rw [hn,Rat.add_mul,Rat.one_mul,Rat.add_comm]

theorem actual_query_envelope (solve : P → Nat → Option (Nat × A)) (q : Nat)
    (js : List (Job P A)) (c : Rat) (hc : 2 ≤ c) :
    actualQueryMass c q (schedule solve q js).calls ≤ queryEnvelope c js := by
  have cp : 0<c := by grind
  by_cases hprune : q < knownCost js+2*pending js
  · rw [schedule_pruned solve q js hprune]
    simp only [actualQueryMass,List.map_nil,List.sum_nil]
    exact Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (Rat.zpow_pos cp))
  · have ht := schedule_trace solve q js
    rw [uniform_query_mass c q (allocated q js) _ ht.2.1]
    have hi := allocation_paid_identity q js (by omega)
    have hd : q-allocated q js=knownCost js+2*(pending js-1) := by omega
    rw [hd]
    exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.2 ht.1)
      (Rat.le_of_lt (Rat.zpow_pos cp))

theorem actual_paid_query_mass (solve : P → Nat → Option (Nat × A)) (q : Nat)
    (js : List (Job P A)) (hbad : 2 ≤ badSlots js) (c : Rat) (hc : 2 ≤ c) :
    actualQueryMass c q (schedule solve q js).calls ≤ c^(-1 : Int) :=
  Rat.le_trans (actual_query_envelope solve q js c hc) (paid_query_envelope c hc js hbad)
end Universal233.PaidQueries
