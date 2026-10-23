import WholeFunctional
import RebasedSourceCounter

namespace CompletedSourceOptimizer20261022
open RMAF Universal233 OrdinaryDispatch
open OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.OptimizerLocalWork
open OrdinaryDispatch.GlobalSourceAssembly OrdinaryDispatch.CompleteSource
open OrdinaryDispatch.RecoveryLocalWork

/-- The new correctness theorem's literal failed prefix is charged in full. -/
theorem retained_trials_work (w : Nat → Nat) (T S : Tree) (q : Nat) (F : CommonForest)
    (tr : (optimize T S).search.trials = failedTrials 0 q ++ [(q,some F)]) :
    trialWork w (optimize T S).search.trials = consecutiveWork w 0 (q+1) := by
  rw [tr]
  simp only [trialWork,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero]
  rw [← trialWork, failed_work, consecutive_snoc]
  simp only [Nat.zero_add]

/-- Query values are certified by the completed original functional theorem. -/
theorem selected_query_exponent (T S : Tree) (hp : DepthOne.proper T S=true)
    (q : Nat) (F : CommonForest) (yes : FastOrdinary.solve q T S=some F) :
    F.length-1≤q := by
  have correct := CompletedFunctional233.query_correct q T S hp
  rw [yes] at correct
  exact correct.2.1

/-- No correctness claim about the old optimizer is used in this summation. -/
theorem retained_trials_bound (T S : Tree) (L q : Nat) (F : CommonForest)
    (hp : DepthOne.proper T S=true)
    (labels : ∀ x, x∈leaves T++leaves S → x<2^L)
    (qn : q<(leaves T).length)
    (tr : (optimize T S).search.trials = failedTrials 0 q ++ [(q,some F)]) :
    (trialWork (fun b=>completeSourceCounter b T S) (optimize T S).search.trials : Rat) ≤
      ((leaves T).length*completeQueryPolynomial (leaves T).length L : Nat)*(233/100:Rat)^q := by
  rw [retained_trials_work _ _ _ _ _ tr]
  have sum := decision_sum_bound (fun b=>completeSourceCounter b T S)
    (fun _ => (completeQueryPolynomial (leaves T).length L : Rat)) q (233/100:Rat)
    (by decide +kernel) Rat.natCast_nonneg (fun _ _ => Rat.le_refl)
    (fun b hb => RebasedSourceCounter20261022.completeSourceQuery_bound T S L hp labels b (by omega))
  have count : ((q+1 : Nat) : Rat) ≤ ((leaves T).length : Rat) :=
    Rat.natCast_le_natCast.2 (by omega)
  have coeff : 0≤(completeQueryPolynomial (leaves T).length L : Rat) := Rat.natCast_nonneg
  have power : 0≤(233/100:Rat)^q := Rat.pow_nonneg (by decide +kernel)
  have enlarged := Rat.mul_le_mul_of_nonneg_right
    (Rat.mul_le_mul_of_nonneg_right count coeff) power
  exact Rat.le_trans sum (by simpa only [Rat.natCast_mul] using enlarged)

theorem retained_wrapper_bound (T S : Tree) (q : Nat) (F : CommonForest)
    (qn : q<(leaves T).length)
    (tr : (optimize T S).search.trials = failedTrials 0 q ++ [(q,some F)]) :
    wrapperCharge (preflightFee (2*(leaves T).length)) 12 32 (optimize T S) ≤
      512*(2*(leaves T).length+1)^2 := by
  have square : 2*(leaves T).length+1 ≤ (2*(leaves T).length+1)^2 := by
    calc
      2*(leaves T).length+1 = (2*(leaves T).length+1)*1 := by omega
      _ ≤ (2*(leaves T).length+1)*(2*(leaves T).length+1) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = (2*(leaves T).length+1)^2 := by simp [Nat.pow_succ]
  have positive : 1≤(2*(leaves T).length+1)^2 := Nat.one_le_pow _ _ (by omega)
  simp only [wrapperCharge,tr,List.length_append,failed_length,List.length_cons,
    List.length_nil,preflightFee]
  omega

/-- Complete SOURCE cost of the literal original optimizer. k is its proved
minimum component count and all failed queries are retained. -/
theorem optimizer_source_bound (T S : Tree) (L : Nat)
    (hp : DepthOne.proper T S=true)
    (labels : ∀ x, x∈leaves T++leaves S → x<2^L) :
    ∃ q F o,
      (completeSourceOptimize T S).value=optimize T S ∧
      (optimize T S).search.selected=some (q,F) ∧
      (optimize T S).search.trials=failedTrials 0 q ++ [(q,some F)] ∧
      (optimize T S).output=some o ∧
      (optimize T S).recoveries=[(F,some o)] ∧
      o.partition.length=q+1 ∧
      (∀ G, agreement T S G=true → o.partition.length≤G.length) ∧
      ((completeSourceOptimize T S).work : Rat) ≤
        (completeOptimizeCoefficient (leaves T).length L : Rat)*
          (233/100:Rat)^(o.partition.length-1) := by
  obtain ⟨q,F,o,sel,tr,out,rec,yes,recovered,af,oaf,realized,edges,valid,cuts,parts,minimum,qn⟩ :=
    CompletedFunctional233.optimization_correct T S hp
  have exp := selected_query_exponent T S hp q F yes
  have checks := af
  simp only [agreement,Bool.and_eq_true] at checks
  have nodup := ((DepthOne.proper_iff T S).1 hp).2.1
  have same := ((DepthOne.proper_iff T S).1 hp).2.2.length_eq
  have recovery := final_source_absorbed S F nodup checks.1.1.1.2 checks.2 q exp
    (233/100:Rat) (by decide +kernel)
  rw [←same] at recovery
  have recoveryBill : (recoverySourceDebit S (optimize T S) : Rat) ≤
      (recoverySourceEnvelope (leaves T).length : Rat)*(233/100:Rat)^q := by
    simpa only [recoverySourceDebit,rec,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,Nat.add_zero] using recovery
  have queries := retained_trials_bound T S L q F hp labels qn tr
  have wrapper := Rat.natCast_le_natCast.2 (retained_wrapper_bound T S q F qn tr)
  have powOne : 1≤(233/100:Rat)^q := by
    simpa using (SourceCoverage.qpow_mono (233/100:Rat) (by decide +kernel) (Nat.zero_le q))
  have wrapperExp := Rat.mul_le_mul_of_nonneg_left powOne
    (show (0:Rat)≤((512*(2*(leaves T).length+1)^2 : Nat):Rat) from Rat.natCast_nonneg)
  simp only [Rat.mul_one] at wrapperExp
  have tn : CoreWork.treeNodes T≤2*(leaves T).length := by
    have h := CoreWork.treeNodes_le_twice_leaves T
    omega
  have sn : CoreWork.treeNodes S≤2*(leaves T).length := by
    have h := CoreWork.treeNodes_le_twice_leaves S
    omega
  have fees := Rat.natCast_le_natCast.2
    (sourceOptimize_actual_fees (fun b=>completeSourceCounter b T S) T S _ tn sn)
  have all := SourceCoverage.qadd_le_add
    (SourceCoverage.qadd_le_add queries (Rat.le_trans wrapper wrapperExp)) recoveryBill
  change ((completeSourceOptimize T S).work : Rat) ≤ _ at fees
  simp only [sourceTotalCharge,Rat.natCast_add] at fees
  have final : ((completeSourceOptimize T S).work : Rat) ≤
      (completeOptimizeCoefficient (leaves T).length L : Rat)*(233/100:Rat)^q := by
    apply Rat.le_trans fees
    simpa only [completeOptimizeCoefficient,Rat.natCast_add,Rat.add_mul] using all
  refine ⟨q,F,o,sourceOptimizeMeter_value _ _ _,sel,tr,out,rec,parts,minimum,?_⟩
  simpa only [parts,Nat.add_sub_cancel] using final

#print axioms retained_trials_work
#print axioms selected_query_exponent
#print axioms retained_trials_bound
#print axioms optimizer_source_bound
end CompletedSourceOptimizer20261022
