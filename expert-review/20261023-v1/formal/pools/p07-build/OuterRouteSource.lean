import UnitCombineBound
namespace OrdinaryDispatch.OuterSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork Universal233.BothBad
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork
open Universal233.Rule5SelectedLocalWork Universal233.Rule5PendantLocalWork Universal233.Hard2Overlap

structure NamedFees where
 rule5 : Nat
 disjoint : Nat
 paid : Result→PaidRoute→Nat

def namedRouteDebit (fees : NamedFees) (T S : Tree) (c : CherryBranching.Candidate) : Hard2Route→Nat
 | .admittedRule5=>fees.rule5
 | .disjointPaid=>fees.disjoint
 | .paid out=>paidNamedDebit (fees.paid out) (paidOuterMeter T S c out).value
 | _=>0

/-- Front graph/disjoint tests are charged by the already sealed front sheet.
This sheet adds only paidCase controls, both unit construction sites, unit
execution/check/minimum and the final answer projection. Named bodies remain
literal residuals; scheduler/disjoint/BothBad costs are not postulated. -/
def routeOuterDebit (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (q : Nat) : Hard2Route→Nat
 | .paid out=>(paidOuterMeter T S c out).work+
  (combineSource actual (fun _ _ _=>0) T S c.a c.b q (Hard2Dispatcher.paidCase actual T S c q out)).work+2
 | _=>0

def routeUnitQueries (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (q : Nat) : Hard2Route→List Query
 | .paid _=>forestQueries actual (Hard2Combine.unitCalls S T c.a c.b q)
 | _=>[]

def executeOuterSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (fees : NamedFees) (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) :
 Hard2Route→Charged (Option (List (List Nat)))
 | .refused=>⟨none,0⟩
 | .direct a=>⟨a,0⟩
 | .admittedRule5=>⟨Hard2Dispatcher.rule5Answer actual T S c.a c.b q,fees.rule5⟩
 | .disjointPaid=>⟨DisjointParents.run actual T S c.a c.b q,fees.disjoint⟩
 | .paid out=>
  let p:=paidCaseSource actual (fees.paid out) T S c q out
  let r:=combineSource actual W T S c.a c.b q p.value
  ⟨r.value.answer,p.work+r.work+2⟩

theorem executeOuterSource_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (fees : NamedFees) (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (route : Hard2Route) :
 (executeOuterSource actual W fees T S c q route).value=executeHard2Route actual T S c q route := by
 cases route <;> simp only [executeOuterSource,executeHard2Route,combineSource_value,paidCaseSource_value]

theorem executeOuterSource_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (fees : NamedFees) (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (route : Hard2Route) :
 (executeOuterSource actual W fees T S c q route).work=
 routeOuterDebit actual T S c q route+namedRouteDebit fees T S c route+
 queryWork W (routeUnitQueries actual T S c q route) := by
 cases route with
 | refused=>rfl
 | direct a=>rfl
 | admittedRule5=>simp only [executeOuterSource,routeOuterDebit,namedRouteDebit,routeUnitQueries,queryWork,List.map_nil,List.sum_nil,Nat.add_zero,Nat.zero_add]
 | disjointPaid=>simp only [executeOuterSource,routeOuterDebit,namedRouteDebit,routeUnitQueries,queryWork,List.map_nil,List.sum_nil,Nat.add_zero,Nat.zero_add]
 | paid out=>
  simp only [executeOuterSource,paidCaseSource_value,paidCaseSource_exact_split,routeOuterDebit,namedRouteDebit,routeUnitQueries]
  rw [combineSource_split]
  omega

def hard2OuterSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (fees : NamedFees)
 (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) : Charged (Option (List (List Nat))) :=
 let f:=hard2FrontMeter T S c q
 let r:=executeOuterSource actual W fees T S c q f.value
 ⟨r.value,f.work+r.work⟩

theorem hard2OuterSource_value (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (fees : NamedFees) (T S : Tree) (c d : CherryBranching.Candidate) (q : Nat) :
 (hard2OuterSource actual W fees T S c q).value=Hard2Dispatcher.run actual T S c d q := by
 simp only [hard2OuterSource,executeOuterSource_value]
 exact hard2FrontMeter_value actual T S c d q

/-- An exact Nat identity, not an assumed upper bound for a missing handler.
The named residual is paid once; only unit ordinary calls are outside it. -/
theorem hard2OuterSource_exact_split (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (fees : NamedFees) (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) :
 (hard2OuterSource actual W fees T S c q).work=
 (hard2FrontMeter T S c q).work+routeOuterDebit actual T S c q (hard2FrontMeter T S c q).value+
 namedRouteDebit fees T S c (hard2FrontMeter T S c q).value+
 queryWork W (routeUnitQueries actual T S c q (hard2FrontMeter T S c q).value) := by
 simp only [hard2OuterSource,executeOuterSource_split]
 omega

def outerCoefficient (N Q : Nat) : Rat:=
 (paidOuterPolynomial (2*N+3):Rat)+combineCoefficient N Q+2

theorem routeOuterDebit_bound (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree}
 {c : CherryBranching.Candidate} (q N Q : Nat) (route : Hard2Route)
 (hp:DepthOne.proper T S=true) (sel:CherryBranching.select T S=some (.hard2,c))
 (size:(leaves T).length≤N) (budget:q≤Q) :
 (routeOuterDebit actual T S c q route:Rat)≤outerCoefficient N Q*Rule5ActualTrace.base^q := by
 have pow:=call_base_pow_ge_one q
 have cn:0≤combineCoefficient N Q:=Rat.add_nonneg Rat.natCast_nonneg
  (Rat.mul_nonneg (by decide +kernel : (0:Rat)≤32) Rat.natCast_nonneg)
 have nn:0≤outerCoefficient N Q:=Rat.add_nonneg (Rat.add_nonneg Rat.natCast_nonneg cn) (by decide +kernel)
 cases route with
 | paid out=>
  have same:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
  have tn:=treeNodes_leafCount T;have sn:=treeNodes_leafCount S
  have p:=Rat.natCast_le_natCast.2 (paidOuterMeter_bound T S c out (2*N+3) (by omega) (by omega))
  have pp:=Rat.mul_le_mul_of_nonneg_left pow (Rat.natCast_nonneg (a:=paidOuterPolynomial (2*N+3)))
  rw [Rat.mul_one] at pp
  have p1:=Rat.le_trans p pp
  have b:=combineSource_local_bound actual q N Q (Hard2Dispatcher.paidCase actual T S c q out) hp sel size budget
   (fun F hF=>(Hard2Dispatcher.paidCase_sound actual T S c q out F hF).2)
  have c2:=Rat.mul_le_mul_of_nonneg_left pow (by decide +kernel : (0:Rat)≤2)
  rw [Rat.mul_one] at c2
  have sum:=Rat.le_trans (Rat.add_le_add_right.mpr (Rat.le_trans (Rat.add_le_add_right.mpr p1) (Rat.add_le_add_left.mpr b))) (Rat.add_le_add_left.mpr c2)
  simpa only [routeOuterDebit,outerCoefficient,Rat.natCast_add,Rat.natCast_ofNat,Rat.add_mul] using sum
 | refused=>exact Rat.mul_nonneg nn (Rat.le_trans (by decide +kernel : (0:Rat)≤1) pow)
 | direct a=>exact Rat.mul_nonneg nn (Rat.le_trans (by decide +kernel : (0:Rat)≤1) pow)
 | admittedRule5=>exact Rat.mul_nonneg nn (Rat.le_trans (by decide +kernel : (0:Rat)≤1) pow)
 | disjointPaid=>exact Rat.mul_nonneg nn (Rat.le_trans (by decide +kernel : (0:Rat)≤1) pow)
end OrdinaryDispatch.OuterSource
