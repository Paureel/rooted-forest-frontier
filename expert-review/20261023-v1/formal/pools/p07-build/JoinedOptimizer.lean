import ReachLocalAssembly
namespace OrdinaryDispatch.GoodPairGlobalAssembly
open RMAF Universal233 WholeSourceWork CoreWork
open OrdinaryDispatch.GlobalSourceAssembly OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.RecoveryLocalWork

/-- Actual optimizer wrapper and source recovery once, using the newly joined
PARTIAL ordinary source bill as its explicit callback charge. -/
def joinedPartialOptimize (T S : Tree) : Charged Execution:=
 sourceOptimizeMeter (fun b=>joinedSourceSubtotal b T S) T S

def joinedOptimizeCoefficient (n L : Nat) : Nat:=
 n*joinedQueryPolynomial n L+512*(2*n+1)^2+recoverySourceEnvelope n

theorem joinedPartialOptimize_value (T S : Tree) :
 (joinedPartialOptimize T S).value=optimize T S:=sourceOptimizeMeter_value _ _ _

theorem joinedPartialOptimize_bound (T S : Tree) (L : Nat) (hp : DepthOne.proper T S=true)
 (labels : ∀x,x∈leaves T++leaves S→x<2^L) :
 ∃o,(optimize T S).output=some o ∧ 0<o.partition.length ∧
 o.sourceCuts.length+1=o.partition.length ∧
 ((joinedPartialOptimize T S).work:Rat)≤
 (joinedOptimizeCoefficient (leaves T).length L:Rat)*(233/100:Rat)^(o.partition.length-1) := by
 have te:=treeNodes_le_twice_leaves T;have se:=treeNodes_le_twice_leaves S
 have same:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
 have tn : treeNodes T≤2*(leaves T).length:=Nat.le_trans (Nat.le_succ _) (Nat.le_of_eq te)
 have sn : treeNodes S≤2*(leaves T).length:=by
  rw [same];exact Nat.le_trans (Nat.le_succ _) (Nat.le_of_eq se)
 simpa only [joinedPartialOptimize,joinedOptimizeCoefficient] using
  sourceOptimize_uniform_233 (fun b=>joinedSourceSubtotal b T S) (joinedQueryPolynomial (leaves T).length L)
   T S (2*(leaves T).length) hp tn sn (joinedSourceQuery_bound T S L hp labels)
end OrdinaryDispatch.GoodPairGlobalAssembly
