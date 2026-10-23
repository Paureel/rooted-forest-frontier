import ChildrenSourceBound
namespace OrdinaryDispatch.FullSourceWork
open RMAF ForestState Universal233 Universal233.CherryBranching
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.FastOrdinary

/-- The actual one/high local source debit at an ordinary invocation. The
proper/pretest guards ensure unreachable branch code is not included. Forest
internal work is present, while ordinary recursive charges are zero here. -/
def simpleLocalDebit (T S : Tree) (q : Nat) : Nat :=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .rejected=>
   let actual:=cutoff FastOrdinary.solve q
   match early T S with
   | .one reverse c=>
    let p:=Oriented reverse T S
    (oneSource actual (fun _ _ _=>0) p.1 p.2 q c.a c.b).work
   | .high reverse c=>
    let p:=Oriented reverse T S
    (highSource actual (fun _ _ _=>0) p.1 p.2 q c.a c.b).work
   | _=>0
  | _=>0
 else 0

theorem simpleLocalDebit_bound (N Q : Nat) (T S : Tree) (q : Nat)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) (budget : q≤Q) :
 (simpleLocalDebit T S q:Rat)≤simpleSourceCoefficient N Q*Rule5ActualTrace.base^q := by
 have nonneg:0≤simpleSourceCoefficient N Q*Rule5ActualTrace.base^q:=
  Rat.mul_nonneg (simpleSourceCoefficient_nonneg N Q)
   (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))
 unfold simpleLocalDebit
 simp only [hp,ite_true]
 cases pre:DepthOne.pretest01 T S with
 | refused=>simpa only [Rat.natCast_ofNat] using nonneg
 | found e=>simpa only [Rat.natCast_ofNat] using nonneg
 | rejected=>
  have sound:=early_sound T S
  cases he:early T S with
  | one reverse c=>
   rw [he] at sound
   have p:=oriented_proper hp reverse
   exact oneSource_local_exponential (cutoff FastOrdinary.solve q) q N Q p sound
    (by rw [oriented_size hp reverse];exact size) budget
  | high reverse c=>
   rw [he] at sound
   have p:=oriented_proper hp reverse
   exact highSource_local_exponential (cutoff FastOrdinary.solve q) q N Q p sound
    (by rw [oriented_size hp reverse];exact size) budget
  | common reverse c=>simpa only [Rat.natCast_ofNat] using nonneg
  | rule4Forward s=>simpa only [Rat.natCast_ofNat] using nonneg
  | rule4Reverse s=>simpa only [Rat.natCast_ofNat] using nonneg
  | hard2 c d=>simpa only [Rat.natCast_ofNat] using nonneg
  | refused=>simpa only [Rat.natCast_ofNat] using nonneg

def simpleTreeSource (q : Nat) (T S : Tree) : Nat := sourceSubtotal simpleLocalDebit q T S

/-- Closed source theorem for this named subtotal through the FULL ordinary
call tree, including calls below hard2/Rule5 nodes. It is not the full runtime
counter: other local branch bodies contribute zero to this subtotal. -/
theorem simpleTreeSource_bound (q : Nat) (T S : Tree) (hp : DepthOne.proper T S=true) :
 (simpleTreeSource q T S:Rat)≤simpleSourceCoefficient (leaves T).length q*
 callNodeFactor*((leaves T).length+1:Nat)*Rule5ActualTrace.base^q := by
 exact sourceSubtotal_bound simpleLocalDebit (leaves T).length q _
  (simpleSourceCoefficient_nonneg _ _) (simpleLocalDebit_bound _ _) q T S (Nat.le_refl _) (Nat.le_refl _) hp

/-- The checked front and completed one/high source subtotal can be combined
without charging recursive ordinary invocations twice. -/
def prefixAndSimpleTreeSource (q : Nat) (T S : Tree) : Nat := prefixTreeWork q T S+simpleTreeSource q T S

theorem prefixAndSimpleTreeSource_bound (q : Nat) (T S : Tree) (hp : DepthOne.proper T S=true) :
 (prefixAndSimpleTreeSource q T S:Rat)≤
 ((prefixCoefficient (leaves T).length:Rat)+simpleSourceCoefficient (leaves T).length q)*
 callNodeFactor*((leaves T).length+1:Nat)*Rule5ActualTrace.base^q := by
 have p:=prefixTreeWork_bound q T S hp
 have s:=simpleTreeSource_bound q T S hp
 have total:=Rat.le_trans (Rat.add_le_add_right.mpr p) (Rat.add_le_add_left.mpr s)
 simpa only [prefixAndSimpleTreeSource,Rat.natCast_add,Rat.add_mul] using total
end OrdinaryDispatch.FullSourceWork
