import RWFinal
namespace OrdinaryDispatch.RecoveryLocalWork
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.OptimizerLocalWork OrdinaryDispatch.BudgetOptimization

/-- The actual selected original forest reaches exactly one now-source-metered
recovery. All failed query trials remain in the frozen optimizer execution. -/
theorem optimizer_recovery_once_bound (T S : Tree) (proper : DepthOne.proper T S=true) :
 ∃q F o,(optimize T S).search.selected=some (q,F) ∧
 (optimize T S).recoveries=[(F,some o)] ∧
 (meterRecover S F).value=some o ∧ F.length=q+1 ∧
 ((optimize T S).recoveries.map (fun call=>(meterRecover S call.1).work)).sum≤
   recoverySourceEnvelope (leaves T).length*2^q := by
 obtain ⟨q,F,o,selected,tr,out,rec,yes,recovered,af,oaf,realized,edges,valid,cuts,parts,minimum,qn⟩:=optimization_exact T S proper
 have chosen : (scan (fun b=>FastOrdinary.solve b T S) 0 (leaves T).length).selected=some (q,F):=by
  simpa only [optimize,proper,ite_true,finish_search] using selected
 have len:=(selected_minimum T S proper q F chosen).2.1
 have checks:=af
 simp only [agreement,Bool.and_eq_true] at checks
 have hn:=((DepthOne.proper_iff T S).1 proper).2.1
 have same:=((DepthOne.proper_iff T S).1 proper).2.2.length_eq
 have bound:=final_source_uniform S F hn checks.1.1.1.2 checks.2
 have qlen:F.length-1=q:=by omega
 rw [qlen,←same] at bound
 refine ⟨q,F,o,selected,rec,by simpa only [meterRecover_value] using recovered,len,?_⟩
 simpa only [rec,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using bound

/-- Exact rational absorption for the one final call. This uses the new source
bill, not FinalCutRecovery.meterRecover's old declared generator bill. -/
theorem optimizer_recovery_233 (T S : Tree) (proper : DepthOne.proper T S=true) :
 ∃q F o,(optimize T S).search.selected=some (q,F) ∧
 (optimize T S).recoveries=[(F,some o)] ∧ (meterRecover S F).value=some o ∧
 (((optimize T S).recoveries.map (fun call=>(meterRecover S call.1).work)).sum:Rat)≤
   (recoverySourceEnvelope (leaves T).length:Rat)*(233/100:Rat)^q := by
 obtain ⟨q,F,o,selected,rec,value,len,bound⟩:=optimizer_recovery_once_bound T S proper
 have rat:=Rat.natCast_le_natCast.2 bound
 rw [Rat.natCast_mul,Rat.natCast_pow] at rat
 have power:=FinalCutRecovery.qpow_base_mono 2 (233/100:Rat) (by decide +kernel) (by decide +kernel) q
 have coeff:0≤(recoverySourceEnvelope (leaves T).length:Rat):=Rat.natCast_le_natCast.2 (Nat.zero_le _)
 exact ⟨q,F,o,selected,rec,value,Rat.le_trans rat (Rat.mul_le_mul_of_nonneg_left power coeff)⟩
end OrdinaryDispatch.RecoveryLocalWork
