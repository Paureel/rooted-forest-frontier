import BOCost
namespace OrdinaryDispatch.BudgetOptimization
open RMAF Universal233

/-- Explicit polynomial coefficient, including the maximum label bit length L. -/
def queryPolynomial (n q L A d : Nat) : Nat := A*(n+q+L+1)^d

def uniformQueryPolynomial (n L A d : Nat) : Nat := A*(2*n+L+1)^d

theorem queryPolynomial_uniform (n q L A d : Nat) (hq : q<n) :
 queryPolynomial n q L A d≤uniformQueryPolynomial n L A d := by
 exact Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega) d)

/-- CONDITIONAL source-operation conversion, not a FastOrdinary runtime proof.
perQuery must eventually be supplied for the actual frozen solve, including
all its recursive work and label/payload costs. The three wrapper charges must
cover their printed primitive operations. For c>=2 the licensed final-recovery
bound is enough; the decision sum itself only requires c>1. -/
theorem conditional_optimization_bound (T S : Tree) (hp : DepthOne.proper T S=true)
 (w : Nat→Nat) (preflight perTrial finishCharge L A d : Nat) (c : Rat) (hc : 2≤c)
 (perQuery : ∀b,b<(leaves T).length →
   (w b:Rat)≤(queryPolynomial (leaves T).length b L A d:Rat)*c^b) :
 ∃q F o,(optimize T S).search.selected=some (q,F) ∧
 (optimize T S).output=some o ∧ FinalCutRecovery.recover S F=some o ∧
 o.partition.length=q+1 ∧ o.sourceCuts.length=q ∧
 totalCharge w preflight perTrial finishCharge S (optimize T S)≤
   (( (leaves T).length*uniformQueryPolynomial (leaves T).length L A d+
      (preflight+perTrial*(leaves T).length+finishCharge)+recoveryEnvelope (leaves T).length:Nat):Rat)*c^q := by
 obtain ⟨q,F,o,sel,out,af,len,charge⟩ := total_charge_exact T S hp w preflight perTrial finishCharge
 have chosen : (scan (fun q => FastOrdinary.solve q T S) 0 (leaves T).length).selected=some (q,F) := by
   simpa [optimize,hp] using sel
 have minimum := selected_minimum T S hp q F chosen
 have qn := minimum.2.2.2.1
 have recovered : FinalCutRecovery.recover S F=some o := by
   simpa [optimize,hp,finish,chosen] using out
 have sound := FinalCutRecovery.recover_sound S F o recovered
 let Q := uniformQueryPolynomial (leaves T).length L A d
 have power : 0≤c^q := Rat.pow_nonneg (by grind)
 have queryBound : ∀b,b≤q → (w b:Rat)≤(Q:Rat)*c^b := by
   intro b hb
   have bn : b<(leaves T).length := by omega
   have coeff := Rat.natCast_le_natCast.2 (queryPolynomial_uniform (leaves T).length b L A d bn)
   exact Rat.le_trans (perQuery b bn)
     (Rat.mul_le_mul_of_nonneg_right coeff (Rat.pow_nonneg (n:=b) (by grind)))
 have checks := af
 simp only [agreement,Bool.and_eq_true] at checks
 have ns := ((DepthOne.proper_iff T S).1 hp).2.1
 have recovery := FinalCutRecovery.final_work_absorbed S F ns checks.1.1.1.2 checks.2 q (by omega) c hc
 have same := ((DepthOne.proper_iff T S).1 hp).2.2.length_eq
 have envelope : recoveryPolynomial S≤recoveryEnvelope (leaves T).length := by
   simpa only [same] using recoveryPolynomial_envelope S
 have uniform := Rat.natCast_le_natCast.2
   (Nat.le_trans (finalPolynomial_uniform S F ns checks.1.1.1.2) envelope)
 have recoveryBound := Rat.le_trans recovery (Rat.mul_le_mul_of_nonneg_right uniform power)
 have full := all_work_bound w (fun _ => (Q:Rat)) q c
   (preflight+perTrial*(q+1)+finishCharge) (recoveryEnvelope (leaves T).length)
   (FinalCutRecovery.meterRecover S F).work (by grind)
   (Rat.natCast_le_natCast.2 (Nat.zero_le _)) (fun _ _ => Rat.le_refl) queryBound recoveryBound
 have qlen : q+1≤(leaves T).length := by omega
 have queryCoeff := Nat.mul_le_mul_right Q qlen
 have wrapperCoeff := Nat.mul_le_mul_left perTrial qlen
 have coeffNat :
   (q+1)*Q+(preflight+perTrial*(q+1)+finishCharge)+recoveryEnvelope (leaves T).length≤
   (leaves T).length*Q+(preflight+perTrial*(leaves T).length+finishCharge)+recoveryEnvelope (leaves T).length := by omega
 have coeff := Rat.natCast_le_natCast.2 coeffNat
 simp only [Rat.natCast_add,Rat.natCast_mul] at coeff
 have lifted := Rat.mul_le_mul_of_nonneg_right coeff power
 refine ⟨q,F,o,sel,out,recovered,by omega,by omega,?_⟩
 rw [charge]
 exact Rat.le_trans full (by simpa [Q,Rat.natCast_add,Rat.natCast_mul] using lifted)

/-- The returned component count is positive, so k-1 conversion cannot use
Nat's truncated subtraction at k=0. This theorem retains the actual output. -/
theorem conditional_k_bound (T S : Tree) (hp : DepthOne.proper T S=true)
 (w : Nat→Nat) (preflight perTrial finishCharge L A d : Nat) (c : Rat) (hc : 2≤c)
 (perQuery : ∀b,b<(leaves T).length →
   (w b:Rat)≤(queryPolynomial (leaves T).length b L A d:Rat)*c^b) :
 ∃o,(optimize T S).output=some o ∧ 0<o.partition.length ∧
 o.sourceCuts.length+1=o.partition.length ∧
 totalCharge w preflight perTrial finishCharge S (optimize T S)≤
   (((leaves T).length*uniformQueryPolynomial (leaves T).length L A d+
      (preflight+perTrial*(leaves T).length+finishCharge)+recoveryEnvelope (leaves T).length:Nat):Rat)*
       c^(o.partition.length-1) := by
 obtain ⟨q,F,o,sel,out,recovered,parts,cuts,bound⟩ :=
   conditional_optimization_bound T S hp w preflight perTrial finishCharge L A d c hc perQuery
 refine ⟨o,out,by omega,by omega,?_⟩
 have eq : o.partition.length-1=q := by omega
 simpa [eq] using bound

/-- Exact rational specialization. The per-query premise remains OPEN. -/
theorem conditional_233 (T S : Tree) (hp : DepthOne.proper T S=true)
 (w : Nat→Nat) (preflight perTrial finishCharge L A d : Nat)
 (perQuery : ∀b,b<(leaves T).length →
   (w b:Rat)≤(queryPolynomial (leaves T).length b L A d:Rat)*(233/100:Rat)^b) :
 ∃o,(optimize T S).output=some o ∧ 0<o.partition.length ∧
 o.sourceCuts.length+1=o.partition.length ∧
 totalCharge w preflight perTrial finishCharge S (optimize T S)≤
   (((leaves T).length*uniformQueryPolynomial (leaves T).length L A d+
      (preflight+perTrial*(leaves T).length+finishCharge)+recoveryEnvelope (leaves T).length:Nat):Rat)*
       (233/100:Rat)^(o.partition.length-1) :=
 conditional_k_bound T S hp w preflight perTrial finishCharge L A d (233/100) (by decide +kernel) perQuery

end OrdinaryDispatch.BudgetOptimization
