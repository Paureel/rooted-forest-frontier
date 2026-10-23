import NamedHandlerJoins
namespace OrdinaryDispatch.OuterSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.GoodPairGlobalAssembly OrdinaryDispatch.GlobalNumeric
open OrdinaryDispatch.ExtendedSourceAssembly OrdinaryDispatch.GlobalSourceAssembly

def outerPolynomial (N Q : Nat) : Nat:=
 paidOuterPolynomial (2*N+3)+combinePolynomial N Q+32*(2^50*(N+Q+2)^8)+2

theorem outerCoefficient_cast (N Q : Nat) : outerCoefficient N Q=(outerPolynomial N Q:Rat) := by
 simp only [outerCoefficient,outerPolynomial,combineCoefficient,unitForestCoefficient,forestCoefficient,
  Rat.natCast_add,Rat.natCast_mul,Rat.natCast_ofNat,Rat.add_assoc]

/-- Only newly owned paidCase/combine/endpoint work is added. The old front,
GoodPair, hardPaid and complete Rule5 bills remain in their existing summands. -/
def outerLocalDebit (T S : Tree) (q : Nat) : Nat:=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .rejected=>match early T S with
   | .hard2 c _=>routeOuterDebit (cutoff FastOrdinary.solve q) T S c q (hard2FrontMeter T S c q).value
   | _=>0
  | _=>0
 else 0

theorem outerLocalDebit_bound (N Q : Nat) (T S : Tree) (q : Nat)
 (hp:DepthOne.proper T S=true) (size:(leaves T).length≤N) (budget:q≤Q) :
 (outerLocalDebit T S q:Rat)≤(outerPolynomial N Q:Rat)*Rule5ActualTrace.base^q := by
 have nn:0≤(outerPolynomial N Q:Rat)*Rule5ActualTrace.base^q:=
  Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))
 unfold outerLocalDebit
 simp only [hp,ite_true]
 cases pre:DepthOne.pretest01 T S with
 | refused=>exact nn
 | found e=>exact nn
 | rejected=>cases he:early T S with
  | hard2 c d=>
   have sound:=early_sound T S;rw [he] at sound
   simpa only [outerCoefficient_cast] using routeOuterDebit_bound (cutoff FastOrdinary.solve q)
    q N Q (hard2FrontMeter T S c q).value hp sound.1 size budget
  | common reverse c=>exact nn
  | one reverse c=>exact nn
  | high reverse c=>exact nn
  | rule4Forward s=>exact nn
  | rule4Reverse s=>exact nn
  | refused=>exact nn

theorem outerLocalDebit_binding (q : Nat) {T S : Tree} (hp:DepthOne.proper T S=true)
 (pre:DepthOne.pretest01 T S=.rejected) {c d : CherryBranching.Candidate} (he:early T S=.hard2 c d) :
 outerLocalDebit T S q=routeOuterDebit (cutoff FastOrdinary.solve q) T S c q (hard2FrontMeter T S c q).value := by
 simp only [outerLocalDebit,hp,ite_true,pre,he]

def outerJoinedLocalDebit (T S : Tree) (q : Nat) : Nat:=joinedLocalSourceDebit T S q+outerLocalDebit T S q
def outerJoinedPolynomial (N Q L : Nat) : Nat:=joinedLocalPolynomial N Q L+outerPolynomial N Q

theorem outerJoinedLocalDebit_reachable_bound (q0 N Q L : Nat) (T0 S0 : Tree)
 (hp0:DepthOne.proper T0 S0=true) (size0:(leaves T0).length≤N) (initialBudget:q0≤Q)
 (labels0:∀x,x∈leaves T0++leaves S0→x<2^L)
 (d : Nat) (T S : Tree) (q : Nat) (path:Reach FastOrdinary.solve q0 T0 S0 d T S q) :
 (outerJoinedLocalDebit T S q:Rat)≤(outerJoinedPolynomial N Q L:Rat)*Rule5ActualTrace.base^q := by
 have domain:=reachableRule5InputDomain q0 N Q L T0 S0 hp0 size0 initialBudget labels0 path
 have cap0:PairCap (2^L) T0 S0:=
  ⟨fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_left _ hx)),
   fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_right _ hx))⟩
 have hp:DepthOne.proper T S=true:=
  (reachable_invariant FastOrdinary.solve q0 N (2^L) T0 S0 hp0 size0 cap0 path).1
 have old:=joinedLocalSourceDebit_reachable_bound q0 N Q L T0 S0 hp0 size0 initialBudget labels0 d T S q path
 have new:=outerLocalDebit_bound N Q T S q hp domain.size domain.budget
 simpa only [outerJoinedLocalDebit,outerJoinedPolynomial,Rat.natCast_add,Rat.add_mul] using rat_add_bounds old new

def outerJoinedSourceSubtotal (q : Nat) (T S : Tree) : Nat:=sourceSubtotal outerJoinedLocalDebit q T S

theorem outerJoinedSourceSubtotal_bound (q0 N Q L : Nat) (T0 S0 : Tree)
 (hp0:DepthOne.proper T0 S0=true) (size0:(leaves T0).length≤N) (initialBudget:q0≤Q)
 (labels0:∀x,x∈leaves T0++leaves S0→x<2^L) :
 (outerJoinedSourceSubtotal q0 T0 S0:Rat)≤(outerJoinedPolynomial N Q L:Rat)*callNodeFactor*
 ((leaves T0).length+1:Nat)*Rule5ActualTrace.base^q0 := by
 exact sourceSubtotal_reach_bound outerJoinedLocalDebit q0 T0 S0 (outerJoinedPolynomial N Q L) Rat.natCast_nonneg
  (outerJoinedLocalDebit_reachable_bound q0 N Q L T0 S0 hp0 size0 initialBudget labels0) hp0 Reach.root

def outerJoinedQueryPolynomial (n L : Nat) : Nat:=outerJoinedPolynomial n n L*1024*(n+1)

theorem outerJoinedSourceQuery_bound (T S : Tree) (L : Nat) (hp:DepthOne.proper T S=true)
 (labels:∀x,x∈leaves T++leaves S→x<2^L) (b : Nat) (budget:b<(leaves T).length) :
 (outerJoinedSourceSubtotal b T S:Rat)≤(outerJoinedQueryPolynomial (leaves T).length L:Rat)*(233/100:Rat)^b := by
 have h:=outerJoinedSourceSubtotal_bound b (leaves T).length (leaves T).length L T S hp (Nat.le_refl _) (Nat.le_of_lt budget) labels
 simpa only [outerJoinedQueryPolynomial,Rat.natCast_mul,Rat.natCast_ofNat,callNodeFactor,Rule5ActualTrace.base] using h
end OrdinaryDispatch.OuterSource
