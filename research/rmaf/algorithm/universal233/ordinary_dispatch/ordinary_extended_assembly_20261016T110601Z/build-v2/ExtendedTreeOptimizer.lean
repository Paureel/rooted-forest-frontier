import HardPaidSelection
import Rule5DispatchJoin
namespace OrdinaryDispatch.ExtendedSourceAssembly
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open OrdinaryDispatch.WorkRecursion OrdinaryDispatch.WorkIntegration OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.RecoveryLocalWork

/-- Bounded PARTIAL sheet: previously closed bills plus actual selected hard-paid
body. paidCase selector, combine, other hard2 handlers and Rule5 remain absent. -/
def extendedLocalDebit (T S : Tree) (q : Nat) : Nat:=closedLocalDebit T S q+hardPaidLocalDebit T S q

def extendedLocalPolynomial (N Q : Nat) : Nat:=closedLocalPolynomial N Q+hardPaidUniformPolynomial (2*N+3) Q

theorem extendedLocalDebit_bound (N Q : Nat) (T S : Tree) (q : Nat)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) (budget : q≤Q) :
 (extendedLocalDebit T S q:Rat)≤(extendedLocalPolynomial N Q:Rat)*Rule5ActualTrace.base^q := by
 have sum:=rat_add_bounds (closedLocalDebit_bound N Q T S q hp size budget)
  (hardPaidLocalDebit_bound N Q T S q hp size budget)
 simpa only [extendedLocalDebit,extendedLocalPolynomial,Rat.natCast_add,Rat.add_mul] using sum

def extendedSourceSubtotal (q : Nat) (T S : Tree) : Nat:=sourceSubtotal extendedLocalDebit q T S

theorem extendedSourceSubtotal_eq (q : Nat) (T S : Tree) :
 extendedSourceSubtotal q T S=extendedLocalDebit T S q+
 queryWork (fun t s r=>extendedSourceSubtotal r t s) (ordinaryStepTrace FastOrdinary.solve q T S).queries:=
 sourceSubtotal_eq extendedLocalDebit q T S

theorem extendedSourceSubtotal_bound (N Q q : Nat) (T S : Tree)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) (budget : q≤Q) :
 (extendedSourceSubtotal q T S:Rat)≤(extendedLocalPolynomial N Q:Rat)*callNodeFactor*
 ((leaves T).length+1:Nat)*Rule5ActualTrace.base^q :=
 sourceSubtotal_bound extendedLocalDebit N Q (extendedLocalPolynomial N Q) Rat.natCast_nonneg
  (extendedLocalDebit_bound N Q) q T S size budget hp

def extendedQueryPolynomial (n : Nat) : Nat:=extendedLocalPolynomial n n*1024*(n+1)

theorem extendedSourceQuery_bound (T S : Tree) (hp : DepthOne.proper T S=true) (b : Nat)
 (budget : b<(leaves T).length) :
 (extendedSourceSubtotal b T S:Rat)≤(extendedQueryPolynomial (leaves T).length:Rat)*(233/100:Rat)^b := by
 have h:=extendedSourceSubtotal_bound (leaves T).length (leaves T).length b T S hp (Nat.le_refl _) (Nat.le_of_lt budget)
 simpa only [extendedQueryPolynomial,Rat.natCast_mul,Rat.natCast_ofNat,callNodeFactor,Rule5ActualTrace.base] using h

/-- The actual optimizer wrapper and new source recovery, with the explicitly
partial extended ordinary callback charge. -/
def extendedPartialOptimize (T S : Tree) : Charged Execution:=
 sourceOptimizeMeter (fun b=>extendedSourceSubtotal b T S) T S

def extendedOptimizeCoefficient (n : Nat) : Nat:=
 n*extendedQueryPolynomial n+512*(2*n+1)^2+recoverySourceEnvelope n

theorem extendedPartialOptimize_value (T S : Tree) :
 (extendedPartialOptimize T S).value=optimize T S:=sourceOptimizeMeter_value _ _ _

theorem extendedPartialOptimize_bound (T S : Tree) (hp : DepthOne.proper T S=true) :
 ∃o,(optimize T S).output=some o ∧ 0<o.partition.length ∧
 o.sourceCuts.length+1=o.partition.length ∧
 ((extendedPartialOptimize T S).work:Rat)≤
 (extendedOptimizeCoefficient (leaves T).length:Rat)*(233/100:Rat)^(o.partition.length-1) := by
 have te:=treeNodes_le_twice_leaves T;have se:=treeNodes_le_twice_leaves S
 have same:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
 have tn : treeNodes T≤2*(leaves T).length:=Nat.le_trans (Nat.le_succ _) (Nat.le_of_eq te)
 have sn : treeNodes S≤2*(leaves T).length:=by
  rw [same];exact Nat.le_trans (Nat.le_succ _) (Nat.le_of_eq se)
 simpa only [extendedPartialOptimize,extendedOptimizeCoefficient] using
  sourceOptimize_uniform_233 (fun b=>extendedSourceSubtotal b T S) (extendedQueryPolynomial (leaves T).length)
   T S (2*(leaves T).length) hp tn sn (extendedSourceQuery_bound T S hp)

/-- Exact residual accounting with the concrete dispatch body also entered.
No bound is claimed for this counter until the external Rule5 closure arrives. -/
def joinedLocalDebit (T S : Tree) (q : Nat) : Nat:=extendedLocalDebit T S q+rule5DispatchLocalDebit T S q

def joinedDispatchSubtotal (q : Nat) (T S : Tree) : Nat:=sourceSubtotal joinedLocalDebit q T S

theorem joinedDispatchSubtotal_eq (q : Nat) (T S : Tree) :
 joinedDispatchSubtotal q T S=joinedLocalDebit T S q+
 queryWork (fun t s r=>joinedDispatchSubtotal r t s) (ordinaryStepTrace FastOrdinary.solve q T S).queries:=
 sourceSubtotal_eq joinedLocalDebit q T S
end OrdinaryDispatch.ExtendedSourceAssembly
