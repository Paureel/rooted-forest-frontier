import Hard2RouteSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.FastOrdinary

/-- Owned hard2 graph and direct/disjoint tests at the actual ordinary code
site. Remaining route execution bodies are separate, explicitly unmetered. -/
def hard2FrontLocalDebit (T S : Tree) (q : Nat) : Nat :=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .rejected=>match early T S with
   | .hard2 c _=>(hard2FrontMeter T S c q).work
   | _=>0
  | _=>0
 else 0

theorem hard2FrontLocalDebit_bound (N : Nat) (T S : Tree) (q : Nat)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) :
 hard2FrontLocalDebit T S q≤hard2FrontCoefficient (2*N+3) := by
 have same:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
 have a:=treeNodes_leafCount T;have b:=treeNodes_leafCount S
 unfold hard2FrontLocalDebit
 simp only [hp,ite_true]
 cases pre:DepthOne.pretest01 T S with
 | refused=>exact Nat.zero_le _
 | found e=>exact Nat.zero_le _
 | rejected=>cases he:early T S with
  | hard2 c d=>exact hard2FrontMeter_bound T S c q (2*N+3) (by omega) (by omega) (by omega)
  | common reverse c=>exact Nat.zero_le _
  | one reverse c=>exact Nat.zero_le _
  | high reverse c=>exact Nat.zero_le _
  | rule4Forward s=>exact Nat.zero_le _
  | rule4Reverse s=>exact Nat.zero_le _
  | refused=>exact Nat.zero_le _

def hard2FrontTreeSource (q : Nat) (T S : Tree) : Nat :=sourceSubtotal hard2FrontLocalDebit q T S

theorem hard2FrontTreeSource_bound (q : Nat) (T S : Tree) (hp : DepthOne.proper T S=true) :
 (hard2FrontTreeSource q T S:Rat)≤(hard2FrontCoefficient (2*(leaves T).length+3):Rat)*
 callNodeFactor*((leaves T).length+1:Nat)*Rule5ActualTrace.base^q := by
 apply sourceSubtotal_bound hard2FrontLocalDebit (leaves T).length q _ Rat.natCast_nonneg
  _ q T S (Nat.le_refl _) (Nat.le_refl _) hp
 intro t s r hp size _
 have localCap:=Rat.natCast_le_natCast.2 (hard2FrontLocalDebit_bound (leaves T).length t s r hp size)
 have scale:=Rat.mul_le_mul_of_nonneg_left (call_base_pow_ge_one r)
  (Rat.natCast_nonneg (a:=hard2FrontCoefficient (2*(leaves T).length+3)))
 rw [Rat.mul_one] at scale
 exact Rat.le_trans localCap scale

/-- Closed accumulated source subtotal: prefix, one/high full forest debits,
and owned hard2 graph/tests. This does not include paid/Rule5 execution bodies. -/
def ordinaryOwnedSourceSubtotal (q : Nat) (T S : Tree) : Nat :=
 prefixAndSimpleTreeSource q T S+hard2FrontTreeSource q T S

theorem ordinaryOwnedSourceSubtotal_bound (q : Nat) (T S : Tree) (hp : DepthOne.proper T S=true) :
 (ordinaryOwnedSourceSubtotal q T S:Rat)≤
 ((prefixCoefficient (leaves T).length:Rat)+simpleSourceCoefficient (leaves T).length q+
  (hard2FrontCoefficient (2*(leaves T).length+3):Rat))*
 callNodeFactor*((leaves T).length+1:Nat)*Rule5ActualTrace.base^q := by
 have a:=prefixAndSimpleTreeSource_bound q T S hp
 have b:=hard2FrontTreeSource_bound q T S hp
 have sum:=Rat.le_trans (Rat.add_le_add_right.mpr a) (Rat.add_le_add_left.mpr b)
 simpa only [ordinaryOwnedSourceSubtotal,Rat.natCast_add,Rat.add_mul] using sum
end OrdinaryDispatch.Hard2SourceWork
