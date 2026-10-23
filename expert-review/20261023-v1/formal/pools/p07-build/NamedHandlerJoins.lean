import OuterRouteSource
import GoodPairRule5Interface
namespace OrdinaryDispatch.OuterSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork Universal233.BothBad
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork
open Universal233.Rule5SelectedLocalWork Universal233.Rule5PendantLocalWork Universal233.Hard2Overlap
open OrdinaryDispatch.FastOrdinary
open Universal233.Rule5ClosedSource

/-- These are the exact still unproved local named-body residuals. They are
visible parameters, never bounded or replaced by a desired callee fee. -/
structure OpenHandlerResiduals where
 disjoint : Nat
 bothBad : PaidRoute→Nat

theorem queryWork_zero (xs : List Query) : queryWork (fun _ _ _=>0) xs=0 := by
 induction xs with
 | nil=>rfl
 | cons a xs ih=>simpa only [queryWork,List.map_cons,List.sum_cons,Nat.zero_add] using ih

def paidBodyDebit (actual : GenericForest.FrontierWork.Ordinary) (W : GenericForest.FrontierWork.OrdinaryWork)
 (openBodies : OpenHandlerResiduals) (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) : PaidRoute→Nat
 | .empty=>0
 | .good X Y Z=>(goodPairSource actual W T S X Y Z q).work
 | .hard=>(hardPaidSource actual W T S q c out).work
 | route@(.bad _ _ _ _)=>openBodies.bothBad route+
   queryWork W (forestQueries actual (paidRouteExecution actual T S c q out route).calls)

theorem paidBodyDebit_split (actual : GenericForest.FrontierWork.Ordinary) (W : GenericForest.FrontierWork.OrdinaryWork)
 (openBodies : OpenHandlerResiduals) (T S : Tree) (c : CherryBranching.Candidate) (q : Nat)
 (out : Result) (route : PaidRoute) :
 paidNamedDebit (paidBodyDebit actual W openBodies T S c q out) route=
 paidNamedDebit (paidBodyDebit actual (fun _ _ _=>0) openBodies T S c q out) route+
 queryWork W (forestQueries actual (paidRouteExecution actual T S c q out route).calls) := by
 cases route with
 | empty=>rfl
 | good X Y Z=>exact goodPairSource_split actual W T S X Y Z q
 | hard=>exact hardPaidSource_split actual W T S q c out
 | bad X Y Z edge=>simp only [paidNamedDebit,paidBodyDebit,queryWork_zero,Nat.add_zero]

def actualNamedFees (W : GenericForest.FrontierWork.OrdinaryWork) (openBodies : OpenHandlerResiduals)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) : NamedFees :=
 let actual:=cutoff FastOrdinary.solve q
 ⟨(admittedRouteSource W T S c q).work,
   openBodies.disjoint+queryWork W (forestQueries actual (Hard2Trace.disjointExecution actual T S c.a c.b q).calls),
   fun out=>paidBodyDebit actual W openBodies T S c q out⟩

def namedRouteQueries (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (q : Nat) : Hard2Route→List Query
 | .admittedRule5=>Rule5ActualTrace.queries actual (Rule5ActualTrace.dispatchTrace actual T S c.a c.b q).calls
 | .disjointPaid=>forestQueries actual (Hard2Trace.disjointExecution actual T S c.a c.b q).calls
 | .paid out=>forestQueries actual (Hard2Dispatcher.paidCase actual T S c q out).calls
 | _=>[]

theorem namedRouteDebit_split (W : GenericForest.FrontierWork.OrdinaryWork) (openBodies : OpenHandlerResiduals)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (route : Hard2Route) :
 namedRouteDebit (actualNamedFees W openBodies T S c q) T S c route=
 namedRouteDebit (actualNamedFees (fun _ _ _=>0) openBodies T S c q) T S c route+
 queryWork W (namedRouteQueries (cutoff FastOrdinary.solve q) T S c q route) := by
 cases route with
 | refused=>rfl
 | direct a=>rfl
 | admittedRule5=>
  have h:=admitted_route_split W T S c q
  rw [actual_rule5_calls_native] at h
  exact h
 | disjointPaid=>simp only [namedRouteDebit,actualNamedFees,namedRouteQueries,queryWork_zero,Nat.add_zero]
 | paid out=>
  have h:=paidBodyDebit_split (cutoff FastOrdinary.solve q) W openBodies T S c q out (paidOuterMeter T S c out).value
  rw [paidOuterMeter_value] at h
  exact h

theorem hard2RouteQueries_decompose (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (q : Nat) (route : Hard2Route) :
 hard2RouteQueries actual T S c q route=
 routeUnitQueries actual T S c q route++namedRouteQueries actual T S c q route := by
 cases route <;> simp only [hard2RouteQueries,routeUnitQueries,namedRouteQueries,Hard2Combine.combine,
  forestQueries,List.flatMap_append,List.nil_append]

/-- Exact source assembly with accepted GoodPair/hardPaid/Rule5 bodies. The
BothBad/disjoint local residuals remain explicit, and every ordinary query
occurrence is charged once. This is not a bound on either open body. -/
theorem actualHard2OuterSource_split (W : GenericForest.FrontierWork.OrdinaryWork) (openBodies : OpenHandlerResiduals)
 (T S : Tree) (c d : CherryBranching.Candidate) (q : Nat) :
 (hard2OuterSource (cutoff FastOrdinary.solve q) W (actualNamedFees W openBodies T S c q) T S c q).work=
 (hard2FrontMeter T S c q).work+
 routeOuterDebit (cutoff FastOrdinary.solve q) T S c q (hard2FrontMeter T S c q).value+
 namedRouteDebit (actualNamedFees (fun _ _ _=>0) openBodies T S c q) T S c (hard2FrontMeter T S c q).value+
 queryWork W (hard2Trace (cutoff FastOrdinary.solve q) T S c d q).queries := by
 rw [hard2OuterSource_exact_split,namedRouteDebit_split]
 rw [←hard2FrontMeter_queries,hard2RouteQueries_decompose]
 simp only [queryWork,List.map_append,List.sum_append]
 omega
end OrdinaryDispatch.OuterSource
