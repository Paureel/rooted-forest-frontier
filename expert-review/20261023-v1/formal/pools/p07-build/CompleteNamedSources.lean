import OuterInterface
import BadPairPolynomialExplicit

namespace OrdinaryDispatch.CompleteSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.OuterSource
open OrdinaryDispatch.FastOrdinary Universal233.BothBad Universal233.Hard2Overlap
open Universal233.Rule5ClosedSource

/-- Literal zero-callback implementations of the two formerly open bodies. -/
def concreteResiduals (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (q : Nat) : OpenHandlerResiduals :=
 ⟨(disjointRunSource actual (fun _ _ _=>0) T S c.a c.b q).work,
  fun route=>match route with
   | .bad X Y Z edge=>(badPairSource actual (fun _ _ _=>0) T S X Y Z edge q).work
   | _=>0⟩

/-- Execute the already licensed source body selected by paidCase. -/
def selectedPaidSource (actual : GenericForest.FrontierWork.Ordinary) (W : GenericForest.FrontierWork.OrdinaryWork)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) : PaidRoute→SourceExecution
 | .empty=>⟨⟨none,[]⟩,0⟩
 | .good X Y Z=>goodPairSource actual W T S X Y Z q
 | .hard=>hardPaidSource actual W T S q c out
 | .bad X Y Z edge=>badPairSource actual W T S X Y Z edge q

theorem selectedPaidSource_value (actual : GenericForest.FrontierWork.Ordinary) (W : GenericForest.FrontierWork.OrdinaryWork)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) (route : PaidRoute) :
 (selectedPaidSource actual W T S c q out route).value=paidRouteExecution actual T S c q out route := by
 cases route with
 | empty=>rfl
 | good X Y Z=>exact goodPairSource_value actual W T S X Y Z q
 | hard=>exact hardPaidSource_value actual W T S q c out
 | bad X Y Z edge=>exact badPairSource_value actual W T S X Y Z edge q

theorem selectedPaidSource_work (actual : GenericForest.FrontierWork.Ordinary) (W : GenericForest.FrontierWork.OrdinaryWork)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) (route : PaidRoute) :
 (selectedPaidSource actual W T S c q out route).work=
 paidNamedDebit (paidBodyDebit actual W (concreteResiduals actual T S c q) T S c q out) route := by
 cases route with
 | empty=>rfl
 | good X Y Z=>rfl
 | hard=>rfl
 | bad X Y Z edge=>exact badPairSource_split actual W T S X Y Z edge q

def paidCaseCompleteSource (actual : GenericForest.FrontierWork.Ordinary) (W : GenericForest.FrontierWork.OrdinaryWork)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) : SourceExecution :=
 let p:=paidOuterMeter T S c out
 let r:=selectedPaidSource actual W T S c q out p.value
 ⟨r.value,p.work+r.work⟩

theorem paidCaseCompleteSource_value (actual : GenericForest.FrontierWork.Ordinary) (W : GenericForest.FrontierWork.OrdinaryWork)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) :
 (paidCaseCompleteSource actual W T S c q out).value=Hard2Dispatcher.paidCase actual T S c q out := by
 simp only [paidCaseCompleteSource,selectedPaidSource_value,paidOuterMeter_value]

theorem paidCaseCompleteSource_bill (actual : GenericForest.FrontierWork.Ordinary) (W : GenericForest.FrontierWork.OrdinaryWork)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) :
 (paidCaseCompleteSource actual W T S c q out).work=
 (paidCaseSource actual (paidBodyDebit actual W (concreteResiduals actual T S c q) T S c q out) T S c q out).work := by
 simp only [paidCaseCompleteSource,selectedPaidSource_work,paidCaseSource]

theorem unitChildren_queryWork (actual : GenericForest.FrontierWork.Ordinary)
 (W : GenericForest.FrontierWork.OrdinaryWork) (T S : Tree) (a b q : Nat) :
 queryWork W (childrenTrace actual T S q [CherryBranching.singletonChild S a,CherryBranching.singletonChild S b]).queries=
 queryWork W (forestQueries actual (Hard2Combine.unitCalls S T a b q)) := by
 have bw:=childForestDebit_as_calls actual W T q [CherryBranching.singletonChild S a,CherryBranching.singletonChild S b]
 have bz:=childForestDebit_as_calls actual (fun _ _ _=>0) T q [CherryBranching.singletonChild S a,CherryBranching.singletonChild S b]
 change childForestDebit actual W T q [CherryBranching.singletonChild S a,CherryBranching.singletonChild S b]=
  callsForestDebit actual W (Hard2Combine.unitCalls S T a b q) at bw
 change childForestDebit actual (fun _ _ _=>0) T q [CherryBranching.singletonChild S a,CherryBranching.singletonChild S b]=
  callsForestDebit actual (fun _ _ _=>0) (Hard2Combine.unitCalls S T a b q) at bz
 have cs:=childForestDebit_split actual W T S q [CherryBranching.singletonChild S a,CherryBranching.singletonChild S b]
 have fs:=callsForestDebit_split actual W (Hard2Combine.unitCalls S T a b q)
 rw [bw,bz] at cs
 omega

theorem disjointRunSource_complete_split (actual : GenericForest.FrontierWork.Ordinary) (W : GenericForest.FrontierWork.OrdinaryWork)
 (T S : Tree) (a b q : Nat) :
 (disjointRunSource actual W T S a b q).work=
 (disjointRunSource actual (fun _ _ _=>0) T S a b q).work+
 queryWork W (forestQueries actual (Hard2Trace.disjointExecution actual T S a b q).calls) := by
 rw [disjointRunSource_split,unitChildren_queryWork]
 simp only [Hard2Trace.disjointExecution,Hard2Combine.combine,forestQueries,List.flatMap_append,
  queryWork,List.map_append,List.sum_append]
 omega

def completeRouteSource (W : GenericForest.FrontierWork.OrdinaryWork) (T S : Tree) (c : CherryBranching.Candidate)
 (q : Nat) : Hard2Route→Charged (Option (List (List Nat)))
 | .refused=>⟨none,0⟩
 | .direct a=>⟨a,0⟩
 | .admittedRule5=>admittedRouteSource W T S c q
 | .disjointPaid=>disjointRunSource (cutoff FastOrdinary.solve q) W T S c.a c.b q
 | .paid out=>
  let p:=paidCaseCompleteSource (cutoff FastOrdinary.solve q) W T S c q out
  let r:=combineSource (cutoff FastOrdinary.solve q) W T S c.a c.b q p.value
  ⟨r.value.answer,p.work+r.work+2⟩

theorem completeRouteSource_value (W : GenericForest.FrontierWork.OrdinaryWork) (T S : Tree) (c : CherryBranching.Candidate)
 (q : Nat) (route : Hard2Route) :
 (completeRouteSource W T S c q route).value=executeHard2Route (cutoff FastOrdinary.solve q) T S c q route := by
 cases route with
 | refused=>rfl
 | direct a=>rfl
 | admittedRule5=>exact admitted_route_value W T S c q
 | disjointPaid=>exact disjointRunSource_value _ _ _ _ _ _ _
 | paid out=>simp only [completeRouteSource,combineSource_value,paidCaseCompleteSource_value,executeHard2Route]

theorem completeRouteSource_bill (W : GenericForest.FrontierWork.OrdinaryWork) (T S : Tree) (c : CherryBranching.Candidate)
 (q : Nat) (route : Hard2Route) :
 (completeRouteSource W T S c q route).work=
 (executeOuterSource (cutoff FastOrdinary.solve q) W
  (actualNamedFees W (concreteResiduals (cutoff FastOrdinary.solve q) T S c q) T S c q) T S c q route).work := by
 cases route with
 | refused=>rfl
 | direct a=>rfl
 | admittedRule5=>rfl
 | disjointPaid=>exact disjointRunSource_complete_split _ _ _ _ _ _ _
 | paid out=>simp only [completeRouteSource,executeOuterSource,actualNamedFees,paidCaseCompleteSource_bill,
   paidCaseCompleteSource_value,paidCaseSource_value]

def hard2CompleteSource (W : GenericForest.FrontierWork.OrdinaryWork) (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) :
 Charged (Option (List (List Nat))) :=
 let f:=hard2FrontMeter T S c q
 let r:=completeRouteSource W T S c q f.value
 ⟨r.value,f.work+r.work⟩

theorem hard2CompleteSource_value (W : GenericForest.FrontierWork.OrdinaryWork) (T S : Tree) (c d : CherryBranching.Candidate) (q : Nat) :
 (hard2CompleteSource W T S c q).value=Hard2Dispatcher.run (cutoff FastOrdinary.solve q) T S c d q := by
 simp only [hard2CompleteSource,completeRouteSource_value]
 exact hard2FrontMeter_value _ _ _ _ _ _

theorem hard2CompleteSource_bill (W : GenericForest.FrontierWork.OrdinaryWork) (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) :
 (hard2CompleteSource W T S c q).work=
 (hard2OuterSource (cutoff FastOrdinary.solve q) W
  (actualNamedFees W (concreteResiduals (cutoff FastOrdinary.solve q) T S c q) T S c q) T S c q).work := by
 simp only [hard2CompleteSource,completeRouteSource_bill,hard2OuterSource]

theorem hard2CompleteSource_split (W : GenericForest.FrontierWork.OrdinaryWork) (T S : Tree) (c d : CherryBranching.Candidate) (q : Nat) :
 (hard2CompleteSource W T S c q).work=(hard2CompleteSource (fun _ _ _=>0) T S c q).work+
 queryWork W (hard2Trace (cutoff FastOrdinary.solve q) T S c d q).queries := by
 rw [hard2CompleteSource_bill,hard2CompleteSource_bill]
 have full:=actualHard2OuterSource_split W (concreteResiduals (cutoff FastOrdinary.solve q) T S c q) T S c d q
 have zero:=actualHard2OuterSource_split (fun _ _ _=>0) (concreteResiduals (cutoff FastOrdinary.solve q) T S c q) T S c d q
 rw [queryWork_zero] at zero
 omega
end OrdinaryDispatch.CompleteSource
