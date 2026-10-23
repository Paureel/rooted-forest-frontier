import CompleteLocalLedger
namespace OrdinaryDispatch.CompleteSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.OuterSource
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.GoodPairGlobalAssembly OrdinaryDispatch.ExtendedSourceAssembly OrdinaryDispatch.GlobalNumeric
open OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.RecoveryLocalWork

def residualPolynomialNat (N Q : Nat) : Nat:=
 disjointRunPolynomial N+badPairLocalPolynomial N Q+32*(2^50*(N+Q+2)^8)

theorem residualForestConstant_le :
 geometric Rule5ActualTrace.base*(2*Rule5ActualTrace.base^(-1:Int)+4*Rule5ActualTrace.base^(-4:Int))+
 (400000000/417428121:Rat)≤32 := by decide +kernel

theorem residualSourcePolynomial_le_nat (N Q : Nat) :
 residualSourcePolynomial N Q≤(residualPolynomialNat N Q:Rat) := by
 have regroup:residualSourcePolynomial N Q=
 ((disjointRunPolynomial N:Rat)+(badPairLocalPolynomial N Q:Rat))+
 (geometric Rule5ActualTrace.base*(2*Rule5ActualTrace.base^(-1:Int)+4*Rule5ActualTrace.base^(-4:Int))+
 (400000000/417428121:Rat))*forestCoefficient N Q:=by
  unfold residualSourcePolynomial disjointSourcePolynomial badPairSourcePolynomial
  have commute:geometric Rule5ActualTrace.base*forestCoefficient N Q*
   (2*Rule5ActualTrace.base^(-1:Int)+4*Rule5ActualTrace.base^(-4:Int))=
   (geometric Rule5ActualTrace.base*(2*Rule5ActualTrace.base^(-1:Int)+4*Rule5ActualTrace.base^(-4:Int)))*forestCoefficient N Q:=by
   rw [Rat.mul_assoc,Rat.mul_comm (forestCoefficient N Q) (2*Rule5ActualTrace.base^(-1:Int)+4*Rule5ActualTrace.base^(-4:Int)),←Rat.mul_assoc]
  rw [commute]
  simp only [Rat.add_mul,Rat.add_assoc,Rat.add_comm,Rat.add_left_comm]
 have scaled:=Rat.mul_le_mul_of_nonneg_right residualForestConstant_le (Rat.natCast_nonneg (a:=2^50*(N+Q+2)^8))
 have total:((disjointRunPolynomial N:Rat)+(badPairLocalPolynomial N Q:Rat))+
 (geometric Rule5ActualTrace.base*(2*Rule5ActualTrace.base^(-1:Int)+4*Rule5ActualTrace.base^(-4:Int))+
 (400000000/417428121:Rat))*forestCoefficient N Q≤
 ((disjointRunPolynomial N:Rat)+(badPairLocalPolynomial N Q:Rat))+32*forestCoefficient N Q:=Rat.add_le_add_left.mpr scaled
 rw [regroup]
 simpa only [residualPolynomialNat,forestCoefficient,Rat.natCast_add,Rat.natCast_mul,Rat.natCast_ofNat] using total

theorem missingLocalDebit_bound (N Q : Nat) (T S : Tree) (q : Nat)
 (hp:DepthOne.proper T S=true) (size:(leaves T).length≤N) (budget:q≤Q) :
 (missingLocalDebit T S q:Rat)≤(residualPolynomialNat (2*N+3) Q:Rat)*Rule5ActualTrace.base^q := by
 have pow:0≤Rule5ActualTrace.base^q:=Rat.le_of_lt (Rat.pow_pos (by decide +kernel))
 have nn:0≤(residualPolynomialNat (2*N+3) Q:Rat)*Rule5ActualTrace.base^q:=Rat.mul_nonneg Rat.natCast_nonneg pow
 unfold missingLocalDebit
 simp only [hp,ite_true]
 cases pre:DepthOne.pretest01 T S with
 | refused=>exact nn
 | found c=>exact nn
 | rejected=>cases he:early T S with
  | common reverse c=>exact nn
  | one reverse c=>exact nn
  | high reverse c=>exact nn
  | rule4Forward s=>exact nn
  | rule4Reverse s=>exact nn
  | refused=>exact nn
  | hard2 c d=>
    have sound:=early_sound T S;rw [he] at sound
    have same:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
    have t:=treeNodes_leafCount T;have s:=treeNodes_leafCount S
    have actual:=selected_route_residual_bound (cutoff FastOrdinary.solve q) q (2*N+3) Q hp sound.1 (by omega) (by omega) budget
    exact Rat.le_trans actual (Rat.mul_le_mul_of_nonneg_right (residualSourcePolynomial_le_nat (2*N+3) Q) pow)

def completeSourcePolynomial (N Q L : Nat) : Nat:=outerJoinedPolynomial N Q L+residualPolynomialNat (2*N+3) Q

theorem completeLocalDebit_reachable_bound (q0 N Q L : Nat) (T0 S0 : Tree)
 (hp0:DepthOne.proper T0 S0=true) (size0:(leaves T0).length≤N) (initialBudget:q0≤Q)
 (labels0:∀x,x∈leaves T0++leaves S0→x<2^L)
 (d : Nat) (T S : Tree) (q : Nat) (path:Reach FastOrdinary.solve q0 T0 S0 d T S q) :
 (completeLocalDebit T S q:Rat)≤(completeSourcePolynomial N Q L:Rat)*Rule5ActualTrace.base^q := by
 have domain:=reachableRule5InputDomain q0 N Q L T0 S0 hp0 size0 initialBudget labels0 path
 have cap0:PairCap (2^L) T0 S0:=
  ⟨fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_left _ hx)),
   fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_right _ hx))⟩
 have hp:DepthOne.proper T S=true:=
  (reachable_invariant FastOrdinary.solve q0 N (2^L) T0 S0 hp0 size0 cap0 path).1
 have old:=outerJoinedLocalDebit_reachable_bound q0 N Q L T0 S0 hp0 size0 initialBudget labels0 d T S q path
 have add:=missingLocalDebit_bound N Q T S q hp domain.size domain.budget
 rw [completeLocalDebit_decomposition q T S hp]
 simpa only [completeSourcePolynomial,Rat.natCast_add,Rat.add_mul] using rat_add_bounds old add

/-- Full actual source counter: its local debit is the actual complete selected
step, and recursion follows every literal source-ordered query occurrence. -/
def completeSourceCounter (q : Nat) (T S : Tree) : Nat:=sourceSubtotal completeLocalDebit q T S

theorem completeSourceCounter_eq (q : Nat) (T S : Tree) :
 completeSourceCounter q T S=completeLocalDebit T S q+
 queryWork (fun t s r=>completeSourceCounter r t s) (ordinaryStepTrace FastOrdinary.solve q T S).queries:=
 sourceSubtotal_eq completeLocalDebit q T S

theorem completeSourceCounter_actual_step (q : Nat) (T S : Tree) :
 completeSourceCounter q T S=
 (ordinaryCompleteStepSource (fun t s r=>completeSourceCounter r t s) q T S).work := by
 rw [ordinaryCompleteStepSource_exact_bill,completeSourceCounter_eq]

theorem completeSourceCounter_bound (q0 N Q L : Nat) (T0 S0 : Tree)
 (hp0:DepthOne.proper T0 S0=true) (size0:(leaves T0).length≤N) (initialBudget:q0≤Q)
 (labels0:∀x,x∈leaves T0++leaves S0→x<2^L) :
 (completeSourceCounter q0 T0 S0:Rat)≤(completeSourcePolynomial N Q L:Rat)*callNodeFactor*
 ((leaves T0).length+1:Nat)*Rule5ActualTrace.base^q0 := by
 exact sourceSubtotal_reach_bound completeLocalDebit q0 T0 S0 (completeSourcePolynomial N Q L) Rat.natCast_nonneg
  (completeLocalDebit_reachable_bound q0 N Q L T0 S0 hp0 size0 initialBudget labels0) hp0 Reach.root

def completeQueryPolynomial (n L : Nat) : Nat:=completeSourcePolynomial n n L*1024*(n+1)

theorem completeSourceQuery_bound (T S : Tree) (L : Nat) (hp:DepthOne.proper T S=true)
 (labels:∀x,x∈leaves T++leaves S→x<2^L) (b : Nat) (budget:b<(leaves T).length) :
 (completeSourceCounter b T S:Rat)≤(completeQueryPolynomial (leaves T).length L:Rat)*(233/100:Rat)^b := by
 have h:=completeSourceCounter_bound b (leaves T).length (leaves T).length L T S hp (Nat.le_refl _) (Nat.le_of_lt budget) labels
 simpa only [completeSourceCounter,completeQueryPolynomial,Rat.natCast_mul,Rat.natCast_ofNat,callNodeFactor,Rule5ActualTrace.base] using h

/-- Original SOURCE optimizer: every actual query uses the full source counter.
Its source recovery remains the original source meter, separate from finite cells. -/
def completeSourceOptimize (T S : Tree) : Charged Execution:=
 sourceOptimizeMeter (fun b=>completeSourceCounter b T S) T S

def completeOptimizeCoefficient (n L : Nat) : Nat:=
 n*completeQueryPolynomial n L+512*(2*n+1)^2+recoverySourceEnvelope n

theorem completeSourceOptimize_value (T S : Tree) :
 (completeSourceOptimize T S).value=optimize T S:=sourceOptimizeMeter_value _ _ _

theorem completeSourceOptimize_bound (T S : Tree) (L : Nat) (hp:DepthOne.proper T S=true)
 (labels:∀x,x∈leaves T++leaves S→x<2^L) :
 ∃o,(optimize T S).output=some o ∧ 0<o.partition.length ∧
 o.sourceCuts.length+1=o.partition.length ∧
 ((completeSourceOptimize T S).work:Rat)≤
 (completeOptimizeCoefficient (leaves T).length L:Rat)*(233/100:Rat)^(o.partition.length-1) := by
 have te:=treeNodes_le_twice_leaves T;have se:=treeNodes_le_twice_leaves S
 have same:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
 have tn:treeNodes T≤2*(leaves T).length:=Nat.le_trans (Nat.le_succ _) (Nat.le_of_eq te)
 have sn:treeNodes S≤2*(leaves T).length:=by
  rw [same];exact Nat.le_trans (Nat.le_succ _) (Nat.le_of_eq se)
 simpa only [completeSourceOptimize,completeOptimizeCoefficient] using
  sourceOptimize_uniform_233 (fun b=>completeSourceCounter b T S) (completeQueryPolynomial (leaves T).length L)
   T S (2*(leaves T).length) hp tn sn (completeSourceQuery_bound T S L hp labels)
end OrdinaryDispatch.CompleteSource
