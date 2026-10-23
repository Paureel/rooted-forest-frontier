import SourceBestRawProjectionV3

namespace SourceOrdinaryMafRawV3
open RMAF Universal233 WholeSourceWork CoreWork
open OrdinaryDispatch.Hard2SourceWork SourceChildMetadataV3

theorem maf_value (actual : GenericForest.FrontierWork.Ordinary)
    (T S : Tree) (U : List Nat) (b : Nat) :
    (mafRecursiveMeter actual T S U b).value=
      MafScheduler.recursive T S (BothBad.asTree (GenericForest.solve actual)) U b := by
  simp only [mafRecursiveMeter,MafScheduler.recursive,BothBad.asTree,restrict_value]
  cases restrict U T <;> cases restrict U S <;> rfl

theorem query_list_value (T S : Tree) (qs : List (List Nat×Nat)) :
    (ordinaryQueriesMeter T S qs).value=qs.filterMap (fun ub=>
      match restrict ub.1 T,restrict ub.1 S with
      | some t,some s=>some (BothBad.Call.mk (some t) [s] ub.2)
      | _,_=>none) := by
  induction qs with
  | nil => rfl
  | cons ub qs ih =>
    simp only [ordinaryQueriesMeter,List.filterMap_cons,restrict_value,ih]
    cases restrict ub.1 T <;> cases restrict ub.1 S <;> rfl

theorem answers_flatten_value (xs : List (Nat×List (List Nat))) :
    (answerFlattenMeter xs).value=xs.flatMap Prod.snd := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [answerFlattenMeter,List.flatMap_cons,ih]

theorem flatten_value (a : Option (List (Nat×List (List Nat)))) :
    (optionFlattenMeter a).value=a.map (fun xs=>xs.flatMap Prod.snd) := by
  cases a <;> simp only [optionFlattenMeter,answers_flatten_value]
  all_goals rfl
end SourceOrdinaryMafRawV3
