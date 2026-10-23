import GoodPairSelectedBound
import ExtendedSourceInterface
namespace OrdinaryDispatch.GoodPairGlobalAssembly
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open OrdinaryDispatch.WorkRecursion OrdinaryDispatch.WorkIntegration OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.ExtendedSourceAssembly OrdinaryDispatch.FastOrdinary
open Universal233.Hard2Overlap Universal233.PaidAssembly

def goodPairUniformPolynomial (N Q : Nat) : Nat:=goodPairPolynomial N+16*(2^50*(N+Q+2)^8)

theorem goodPairSource_uniform (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (o : Order) (edge : RMAF.Vertex×RMAF.Vertex) (p r : RMAF.Vertex)
 (q N Q : Nat) (three : 3≤N) (budget : q≤Q) (tn : treeNodes T≤N) (sn : treeNodes S≤N)
 (hp : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (cuts : c.originalCuts=[p,r]) (selected : runHard2 T S c=some (.pair o (.edge edge)))
 (good : (restrictionAgrees S T (first o (leftParent S p) (rightParent S r) (rootParent S p r)) &&
  restrictionAgrees S T (second o (leftParent S p) (rightParent S r) (rootParent S p r)))=true) :
 ((goodPairSource actual (fun _ _ _=>0) T S
  (first o (leftParent S p) (rightParent S r) (rootParent S p r))
  (second o (leftParent S p) (rightParent S r) (rootParent S p r))
  (third o (leftParent S p) (rightParent S r) (rootParent S p r)) q).work:Rat)≤
 (goodPairUniformPolynomial N Q:Rat)*Rule5ActualTrace.base^q := by
 have old:=selected_goodPairSource_bound actual T S c o edge p r q N Q three budget tn sn hp hard cuts selected good
 have fn:0≤forestCoefficient N Q:=Rat.natCast_nonneg
 have gn:0≤geometric Rule5ActualTrace.base:=(geometric_properties _ (by decide +kernel)).2.2.1
 have a:=Rat.mul_le_mul_of_nonneg_left (show Rule5ActualTrace.base^(-3:Int)≤1 by decide +kernel) (Rat.mul_nonneg gn fn)
 have b:=Rat.mul_le_mul_of_nonneg_right (show geometric Rule5ActualTrace.base≤16 by decide +kernel) fn
 have coef:geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^(-3:Int)≤16*forestCoefficient N Q:=
  Rat.le_trans a (by simpa only [Rat.mul_one] using b)
 have added : (goodPairPolynomial N:Rat)+geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^(-3:Int)≤
  (goodPairPolynomial N:Rat)+16*forestCoefficient N Q:=Rat.add_le_add_left.mpr coef
 have scaled:=Rat.mul_le_mul_of_nonneg_right added (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))
 apply Rat.le_trans old
 simpa only [goodPairUniformPolynomial,forestCoefficient,Rat.natCast_add,Rat.natCast_mul,Rat.natCast_ofNat] using scaled

/-- A selected-body subtotal only; the paidCase tests remain a separate bill. -/
def goodPairSelectedDebit (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (out : Hard2Overlap.Result) (q : Nat) : Nat:=
 match c.originalCuts with
 | [p,r]=>
  match out with
  | .pair o (.edge _) =>
   let X:=first o (leftParent S p) (rightParent S r) (rootParent S p r)
   let Y:=second o (leftParent S p) (rightParent S r) (rootParent S p r)
   let Z:=third o (leftParent S p) (rightParent S r) (rootParent S p r)
   if restrictionAgrees S T X && restrictionAgrees S T Y then
    (goodPairSource actual (fun _ _ _=>0) T S X Y Z q).work else 0
  | _=>0
 | _=>0

theorem goodPairSelectedDebit_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (out : Hard2Overlap.Result) (q N Q : Nat)
 (three : 3≤N) (budget : q≤Q) (tn : treeNodes T≤N) (sn : treeNodes S≤N)
 (hp : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (selected : runHard2 T S c=some out) :
 (goodPairSelectedDebit actual T S c out q:Rat)≤(goodPairUniformPolynomial N Q:Rat)*Rule5ActualTrace.base^q := by
 have nonneg:0≤(goodPairUniformPolynomial N Q:Rat)*Rule5ActualTrace.base^q:=
  Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))
 unfold goodPairSelectedDebit
 split
 · rename_i p r cuts
   cases out with
   | disjoint=>simpa only [Rat.natCast_ofNat] using nonneg
   | clique v=>simpa only [Rat.natCast_ofNat] using nonneg
   | four o v w=>simpa only [Rat.natCast_ofNat] using nonneg
   | diagonal o v w=>simpa only [Rat.natCast_ofNat] using nonneg
   | pair o k=>cases k with
    | vertex v=>simpa only [Rat.natCast_ofNat] using nonneg
    | edge e=>
     dsimp only
     split
     · rename_i good
       exact goodPairSource_uniform actual T S c o e p r q N Q three budget tn sn hp hard cuts selected good
     · simpa only [Rat.natCast_ofNat] using nonneg
 · simpa only [Rat.natCast_ofNat] using nonneg

def goodPairLocalDebit (T S : Tree) (q : Nat) : Nat:=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .rejected=>match early T S with
   | .hard2 c _=>match runHard2 T S c with
    | some out=>goodPairSelectedDebit (cutoff FastOrdinary.solve q) T S c out q
    | none=>0
   | _=>0
  | _=>0
 else 0

theorem goodPairLocalDebit_bound (N Q : Nat) (T S : Tree) (q : Nat)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) (budget : q≤Q) :
 (goodPairLocalDebit T S q:Rat)≤(goodPairUniformPolynomial (2*N+3) Q:Rat)*Rule5ActualTrace.base^q := by
 have nonneg:0≤(goodPairUniformPolynomial (2*N+3) Q:Rat)*Rule5ActualTrace.base^q:=
  Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))
 have same:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
 have tn:=treeNodes_leafCount T;have sn:=treeNodes_leafCount S
 unfold goodPairLocalDebit
 simp only [hp,ite_true]
 cases pre:DepthOne.pretest01 T S with
 | refused=>simpa only [Rat.natCast_ofNat] using nonneg
 | found e=>simpa only [Rat.natCast_ofNat] using nonneg
 | rejected=>cases he:early T S with
  | hard2 c d=>
   dsimp only
   have sound:=early_sound T S;rw [he] at sound
   cases selected:runHard2 T S c with
   | none=>simpa only [selected,Rat.natCast_ofNat] using nonneg
   | some out=>
    simp only [selected]
    exact goodPairSelectedDebit_bound (cutoff FastOrdinary.solve q) T S c out q (2*N+3) Q
     (by omega) budget (by omega) (by omega) hp sound.1 selected
  | common reverse c=>simpa only [Rat.natCast_ofNat] using nonneg
  | one reverse c=>simpa only [Rat.natCast_ofNat] using nonneg
  | high reverse c=>simpa only [Rat.natCast_ofNat] using nonneg
  | rule4Forward s=>simpa only [Rat.natCast_ofNat] using nonneg
  | rule4Reverse s=>simpa only [Rat.natCast_ofNat] using nonneg
  | refused=>simpa only [Rat.natCast_ofNat] using nonneg
end OrdinaryDispatch.GoodPairGlobalAssembly
