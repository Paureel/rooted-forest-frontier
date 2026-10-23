import GoodPairStepJoin
import ClosedRule5Join
namespace OrdinaryDispatch.GoodPairGlobalAssembly
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open OrdinaryDispatch.WorkRecursion OrdinaryDispatch.WorkIntegration OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.ExtendedSourceAssembly OrdinaryDispatch.GlobalNumeric Universal233.Rule5ClosedSource

/-- Extended actual local subtotal. The old dispatch-only Rule5 residual is not
added: the completed caller already includes that body and its forest debits. -/
def joinedLocalSourceDebit (T S : Tree) (q : Nat) : Nat:=
 extendedLocalDebit T S q+goodPairLocalDebit T S q+closedRule5LocalDebit T S q

def joinedLocalPolynomial (N Q L : Nat) : Nat:=
 extendedLocalPolynomial N Q+goodPairUniformPolynomial (2*N+3) Q+C5 N Q (semanticWidth N L Q)

theorem joinedLocalSourceDebit_reachable_bound (q0 N Q L : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N) (initialBudget : q0≤Q)
 (labels0 : ∀x,x∈leaves T0++leaves S0→x<2^L)
 (d : Nat) (T S : Tree) (q : Nat) (path : Reach FastOrdinary.solve q0 T0 S0 d T S q) :
 (joinedLocalSourceDebit T S q:Rat)≤(joinedLocalPolynomial N Q L:Rat)*Rule5ActualTrace.base^q := by
 have domain:=reachableRule5InputDomain q0 N Q L T0 S0 hp0 size0 initialBudget labels0 path
 have cap0 : PairCap (2^L) T0 S0:=
  ⟨fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_left _ hx)),
   fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_right _ hx))⟩
 have hp:DepthOne.proper T S=true:=
  (reachable_invariant FastOrdinary.solve q0 N (2^L) T0 S0 hp0 size0 cap0 path).1
 have e:=extendedLocalDebit_bound N Q T S q hp domain.size domain.budget
 have g:=goodPairLocalDebit_bound N Q T S q hp domain.size domain.budget
 have f:=closedRule5LocalDebit_bound N Q (semanticWidth N L Q) T S q hp domain.size domain.budget
  domain.targetLabels domain.sourceLabels
 have sum:=rat_add_bounds (rat_add_bounds e g) f
 simpa only [joinedLocalSourceDebit,joinedLocalPolynomial,Rat.natCast_add,Rat.add_mul] using sum

/-- Every actual invocation contributes all newly licensed local sheets once.
Missing scheduler/disjoint/BothBad/paidCase/combine sheets remain absent. -/
def joinedSourceSubtotal (q : Nat) (T S : Tree) : Nat:=sourceSubtotal joinedLocalSourceDebit q T S

theorem joinedSourceSubtotal_eq (q : Nat) (T S : Tree) :
 joinedSourceSubtotal q T S=joinedLocalSourceDebit T S q+
 queryWork (fun t s r=>joinedSourceSubtotal r t s) (ordinaryStepTrace FastOrdinary.solve q T S).queries:=
 sourceSubtotal_eq joinedLocalSourceDebit q T S

theorem joinedSourceSubtotal_bound (q0 N Q L : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N) (initialBudget : q0≤Q)
 (labels0 : ∀x,x∈leaves T0++leaves S0→x<2^L) :
 (joinedSourceSubtotal q0 T0 S0:Rat)≤(joinedLocalPolynomial N Q L:Rat)*callNodeFactor*
 ((leaves T0).length+1:Nat)*Rule5ActualTrace.base^q0 := by
 exact sourceSubtotal_reach_bound joinedLocalSourceDebit q0 T0 S0 (joinedLocalPolynomial N Q L) Rat.natCast_nonneg
  (joinedLocalSourceDebit_reachable_bound q0 N Q L T0 S0 hp0 size0 initialBudget labels0) hp0 Reach.root

def joinedQueryPolynomial (n L : Nat) : Nat:=joinedLocalPolynomial n n L*1024*(n+1)

theorem joinedSourceQuery_bound (T S : Tree) (L : Nat) (hp : DepthOne.proper T S=true)
 (labels : ∀x,x∈leaves T++leaves S→x<2^L) (b : Nat) (budget : b<(leaves T).length) :
 (joinedSourceSubtotal b T S:Rat)≤(joinedQueryPolynomial (leaves T).length L:Rat)*(233/100:Rat)^b := by
 have h:=joinedSourceSubtotal_bound b (leaves T).length (leaves T).length L T S hp (Nat.le_refl _) (Nat.le_of_lt budget) labels
 simpa only [joinedQueryPolynomial,Rat.natCast_mul,Rat.natCast_ofNat,callNodeFactor,Rule5ActualTrace.base] using h
end OrdinaryDispatch.GoodPairGlobalAssembly
