import HardPaidSourceBound
import GuardCost
namespace OrdinaryDispatch.Hard2SourceWork
open OrdinaryDispatch.WorkRecursion
open RMAF ForestState ForestGroups Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.WorkIntegration
open Universal233.BothBad Universal233.Rule5SelectedLocalWork

/-- Each literal A++B expression pays its own left-list traversal/copy. -/
def appendLabelsMeter (A B : List Nat) : Charged (List Nat):=⟨A++B,2*A.length+4⟩
@[simp] theorem appendLabelsMeter_value (A B : List Nat) : (appendLabelsMeter A B).value=A++B:=rfl

def localTargetMeter (T : Option Tree) (U : List Nat) : Charged (Option Tree) :=
 match T with
 | none=>⟨none,2⟩
 | some t=>let r:=meterRestrict U t;⟨r.value,r.work+4⟩
@[simp] theorem localTargetMeter_value (T : Option Tree) (U : List Nat) :
 (localTargetMeter T U).value=localTarget T U:=by cases T <;> simp [localTargetMeter,localTarget]

/-- The literal owned filter recomputes leaves at every source occurrence. -/
def ownedMeter (ss : List Tree) (U : List Nat) : Charged (List Tree) :=
 meterFilter (fun s=>let l:=meterLeaves s;let c:=meterContained l.value U
  ⟨c.value,l.work+c.work+4⟩) ss
@[simp] theorem ownedMeter_value (ss : List Tree) (U : List Nat) :
 (ownedMeter ss U).value=owned ss U:=by simp [ownedMeter,owned]

def additionalCostMeter (ss : List Tree) (F : List (List Nat)) : Charged Nat:=
 ⟨F.length-ss.length,F.length+ss.length+4⟩
@[simp] theorem additionalCostMeter_value (ss : List Tree) (F : List (List Nat)) :
 (additionalCostMeter ss F).value=additionalCost ss F:=rfl

/-- Original callback forest work is charged once for every literal call. -/
def callsForestDebit (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (calls : List Call) : Nat:=
 (calls.map fun call=>forestWork actual W call.target call.sources call.budget).sum

theorem callsForestDebit_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (calls : List Call) :
 callsForestDebit actual W calls=callsForestDebit actual (fun _ _ _=>0) calls+
 queryWork W (forestQueries actual calls):=by
 induction calls with
 | nil=>rfl
 | cons a calls ih=>
  simp only [callsForestDebit,List.map_cons,List.sum_cons] at ih ⊢
  rw [forestWork_split]
  simp only [forestQueries,List.flatMap_cons,queryWork,List.map_append,List.sum_append] at ih ⊢
  omega
end OrdinaryDispatch.Hard2SourceWork
