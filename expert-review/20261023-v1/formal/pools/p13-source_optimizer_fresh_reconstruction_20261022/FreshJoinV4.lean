/- One-shot independently authored optimizer join. Supplied counter/correctness/support
   results are shared assumptions at their exact licensed TYPES, not reconstructed. -/
import FreshJoinV3
namespace FreshOptimizerJoin20261022
open RMAF Universal233 OrdinaryDispatch Universal233.CoreWork
open OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.CompleteSource
open OrdinaryDispatch.GlobalSourceAssembly OrdinaryDispatch.OptimizerLocalWork
open OrdinaryDispatch.RecoveryLocalWork

def coefficient (n L : Nat) : Nat :=
 n*completeQueryPolynomial n L + 512*(2*n+1)^2 + recoverySourceEnvelope n

theorem optimizer_source_join (T S : Tree) (L : Nat)
 (hp : DepthOne.proper T S = true)
 (labels : ∀ x, x ∈ leaves T ++ leaves S → x < 2^L) :
 ∃ (k : Nat) (F : CommonForest) (o : CoreProgram.Output),
   0 < k ∧ agreement T S o.partition = true ∧
   (∀ G, agreement T S G = true → k ≤ G.length) ∧
   (optimize T S).output = some o ∧ o.partition.length = k ∧
   CutRealization.RealizedOutput S o ∧
   (sourceOptimizeMeter (fun b => completeSourceCounter b T S) T S).value = optimize T S ∧
   ((sourceOptimizeMeter (fun b => completeSourceCounter b T S) T S).work : Rat) ≤
     (coefficient (leaves T).length L : Rat) * (233/100 : Rat)^(k-1) ∧
   (optimize T S).search.trials = failedTrials 0 (k-1) ++ [(k-1,some F)] ∧
   (optimize T S).recoveries = [(F,some o)] := by
 obtain ⟨q,F,o,hselected,htrials,hout,hrec,hsolve,hrecover,hF,ho,hreal,
   hcuts,hvalid,hqlen,holen,hmin,hqn⟩ := CompletedFunctional233.optimization_correct T S hp
 let n := (leaves T).length
 let w := fun b => completeSourceCounter b T S
 let P := completeQueryPolynomial n L
 let A := 512*(2*n+1)^2
 let R := recoverySourceEnvelope n
 have parts := proper_parts T S hp
 have hSn : (leaves S).length = n := parts.2.2.length_eq.symm
 have tn : treeNodes T ≤ 2*n := by have h := nodes_identity T; dsimp [n]; omega
 have sn : treeNodes S ≤ 2*n := by have h := nodes_identity S; omega
 have actual := sourceOptimize_actual_fees w T S (2*n) tn sn
 have hlen : (optimize T S).search.trials.length = q+1 := by
   simp [htrials, failed_length]
 have hbud : ∀ t ∈ (optimize T S).search.trials, t.1 ≤ q := by
   intro t ht
   rw [htrials] at ht
   simp only [List.mem_append, List.mem_singleton] at ht
   rcases ht with ht | ht
   · have h := failed_budgets 0 q t ht; omega
   · subst t; omega
 have hquery : ∀ b, b ≤ q → (w b:Rat) ≤ (P:Rat)*Rule5ActualTrace.base^q := by
   intro b hb
   have hn : b ≤ n := by omega
   have h := RebasedSourceCounter20261022.completeSourceCounter_bound b n n L T S hp
     (Nat.le_refl n) hn labels
   have h' : (w b:Rat) ≤ (P:Rat)*Rule5ActualTrace.base^b := by
     simpa [w, P, completeQueryPolynomial, OrdinaryDispatch.WorkRecursion.callNodeFactor,
       Rat.mul_assoc] using h
   exact Rat.le_trans h' (Rat.mul_le_mul_of_nonneg_left (base_mono b q hb) Rat.natCast_nonneg)
 have hsum := trials_sum_bound w (optimize T S).search.trials
   ((P:Rat)*Rule5ActualTrace.base^q) (fun t ht => hquery t.1 (hbud t ht))
 have hlenN : (optimize T S).search.trials.length ≤ n := by omega
 have hsum' : (trialWork w (optimize T S).search.trials:Rat) ≤
   (n:Rat)*(P:Rat)*Rule5ActualTrace.base^q := by
   apply Rat.le_trans hsum
   simpa only [Rat.mul_assoc] using
     Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hlenN)
       (Rat.mul_nonneg Rat.natCast_nonneg (Rat.pow_nonneg (by unfold Rule5ActualTrace.base; decide +kernel)))
 have hwrapN : wrapperCharge (preflightFee (2*n)) 12 32 (optimize T S) ≤ A := by
   simpa only [wrapperCharge, hlen, A] using wrapper_bound n q hqn
 have hwrap : (wrapperCharge (preflightFee (2*n)) 12 32 (optimize T S):Rat) ≤
   (A:Rat)*Rule5ActualTrace.base^q := by
   apply Rat.le_trans (Rat.natCast_le_natCast.mpr hwrapN)
   simpa only [Rat.mul_one] using Rat.mul_le_mul_of_nonneg_left (base_one q) (Rat.natCast_nonneg (a:=A))
 have hag := hF
 simp only [agreement, Bool.and_eq_true] at hag
 have hpFS : partitionCheck (leaves S) F = true := hag.1.1.1.2
 have heFS : pairwiseEmbeddings S F = true := hag.2
 have hqe := CompletedFunctional233.query_correct q T S hp
 rw [hsolve] at hqe
 change agreement T S F = true ∧ F.length-1 ≤ q ∧ _ at hqe
 have hr := final_source_absorbed S F parts.2.1 hpFS heFS q hqe.2.1
   Rule5ActualTrace.base (by unfold Rule5ActualTrace.base; decide +kernel)
 have hr' : ((meterRecover S F).work:Rat) ≤ (R:Rat)*Rule5ActualTrace.base^q := by
   simpa only [hSn, R] using hr
 have hdebit : recoverySourceDebit S (optimize T S) = (meterRecover S F).work := by
   simp [recoverySourceDebit, hrec]
 have htotal : (sourceTotalCharge w (preflightFee (2*n)) 12 32 S (optimize T S):Rat) ≤
   (coefficient n L:Rat)*Rule5ActualTrace.base^q := by
   have hsumall := add_le_add (add_le_add hsum' hwrap) hr'
   simpa only [sourceTotalCharge, hdebit, coefficient, P, A, R,
     Rat.natCast_add, Rat.natCast_mul, Rat.add_mul, Rat.mul_assoc] using hsumall
 have hw := Rat.le_trans (Rat.natCast_le_natCast.mpr actual) htotal
 refine ⟨q+1,F,o,by omega,ho,?_,hout,holen,hreal,sourceOptimizeMeter_value w T S,?_,?_,hrec⟩
 · intro G hG
   simpa only [holen] using hmin G hG
 · simpa only [Nat.add_sub_cancel, Rule5ActualTrace.base] using hw
 · simpa only [Nat.add_sub_cancel] using htrials

#print axioms optimizer_source_join
end FreshOptimizerJoin20261022
