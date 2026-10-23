import OrdinaryMafRawProjectionV3

namespace SourceOrdinaryMafRawV3
open RMAF Universal233 WholeSourceWork CoreWork PaidQueries
open OrdinaryDispatch.Hard2SourceWork SourceSchedulerRawV3

theorem maf_schedule_retained (actual : GenericForest.FrontierWork.Ordinary)
    (T S : Tree) (q : Nat) (js : List (Job (List Nat) (List (List Nat)))) :
    (scheduleSourceMeter (mafRecursiveMeter actual T S) q js).value=
      (meterSchedule (MafScheduler.recursive T S (BothBad.asTree (GenericForest.solve actual)))
        (fun _ _=>0) q js).value ∧
    (scheduleSourceMeter (mafRecursiveMeter actual T S) q js).queries=
      (meterSchedule (MafScheduler.recursive T S (BothBad.asTree (GenericForest.solve actual)))
        (fun _ _=>0) q js).queries := by
  have hf:(fun U b=>(mafRecursiveMeter actual T S U b).value)=
      MafScheduler.recursive T S (BothBad.asTree (GenericForest.solve actual)) := by
    funext U b
    exact maf_value actual T S U b
  have hv:=schedule_retained (mafRecursiveMeter actual T S) (fun _ _=>0) q js
  rw [hf] at hv
  exact hv
end SourceOrdinaryMafRawV3
