import CommonActualJobs
namespace Universal233.Rule5ClosedSource
open RMAF CoreGraph Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryDispatch.FullSourceWork WholeSourceWork CoreWork
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5SelectedLocalWork
open ClassifierCheckFee PaidLiteralDecisionWork

theorem source_refused_work (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b q L : Nat)
 (sel:(finalMeter checkFee T S a b).value=none)
 (tlabs:∀x,x∈leaves T→x<2^L) (slabs:∀x,x∈leaves S→x<2^L) :
 (rule5AnswerSource cb W T S a b q).work≤finalBudget (leaves T).length (leaves S).length
  (checkCap ((leaves T).length+(leaves S).length))+4 := by
 have h:=final_source_work T S a b L tlabs slabs
 simpa only [rule5AnswerSource,source,dispatchSource,sel,finalSourceMeter,Nat.add_assoc,Nat.reduceAdd] using Nat.add_le_add_right h 4

theorem selector_refused_bound (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b q N Q L : Nat)
 (sel:(finalMeter checkFee T S a b).value=none) (tn:(leaves T).length≤N) (sn:(leaves S).length≤N)
 (tlabs:∀x,x∈leaves T→x<2^L) (slabs:∀x,x∈leaves S→x<2^L) :
 ((rule5AnswerSource cb W T S a b q).work:Rat)≤(C5 N Q L:Rat)*(233/100:Rat)^q := by
 have h:=source_refused_work cb W T S a b q L sel tlabs slabs
 have mono:=final_budget_mono tn sn (check_cap_mono (show (leaves T).length+(leaves S).length≤2*N by omega))
 have cap:(rule5AnswerSource cb W T S a b q).work≤prefixCap N:=by unfold prefixCap;omega
 have c:(rule5AnswerSource cb W T S a b q).work≤C5 N Q L:=by unfold C5;omega
 have cr:=Rat.natCast_le_natCast.2 c
 have pow:=call_base_pow_ge_one q
 have scale:=Rat.mul_le_mul_of_nonneg_left pow (Rat.natCast_nonneg (a:=C5 N Q L))
 rw [Rat.mul_one] at scale
 simpa only [Rule5ActualTrace.base] using Rat.le_trans cr scale
end Universal233.Rule5ClosedSource
