import PartitionCost
import SourceWork
namespace GenericForest.CheckCorrespondence
open RMAF ForestState Universal233 WholeSourceWork CoreWork

def meterSameShape : Tree → Tree → Charged Bool
 | .leaf a,.leaf b => ⟨a==b,4⟩
 | .node a b,.node c d =>
  let ac:=meterSameShape a c;let bd:=meterSameShape b d;let ad:=meterSameShape a d;let bc:=meterSameShape b c
  ⟨(ac.value && bd.value)||(ad.value && bc.value),ac.work+bd.work+ad.work+bc.work+4⟩
 | _,_ => ⟨false,4⟩

@[simp] theorem meterSameShape_value (T S : Tree) : (meterSameShape T S).value=sameShape T S := by
 induction T generalizing S with
 | leaf x => cases S <;> rfl
 | node l r ihl ihr => cases S <;> simp [meterSameShape,sameShape,ihl,ihr]

theorem meterSameShape_work (T S : Tree) : (meterSameShape T S).work=4*Rule5Classification.shapeWork T S := by
 induction T generalizing S with
 | leaf x => cases S <;> rfl
 | node l r ihl ihr =>
  cases S with
  | leaf x => rfl
  | node a b => simp only [meterSameShape,Rule5Classification.shapeWork,ihl,ihr,Nat.mul_add];omega

theorem treeSize_nodes (T : Tree) : Rule5Classification.treeSize T=treeNodes T := by
 induction T <;> simp_all [Rule5Classification.treeSize,treeNodes]

theorem meterSameShape_bound (T S : Tree) : (meterSameShape T S).work≤4*treeNodes T*treeNodes S := by
 rw [meterSameShape_work]
 have h:=Nat.mul_le_mul_left 4 (Rule5Classification.shapeWork_bound T S)
 simpa only [treeSize_nodes,Nat.mul_assoc] using h

def meterRestrict (B : List Nat) : Tree → Charged (Option Tree)
 | .leaf x => let m:=meterContains x B;⟨if m.value then some (.leaf x) else none,m.work+4⟩
 | .node l r =>
  let a:=meterRestrict B l;let b:=meterRestrict B r
  ⟨match a.value,b.value with
   | none,none=>none | some x,none=>some x | none,some y=>some y | some x,some y=>some (.node x y),a.work+b.work+4⟩

@[simp] theorem meterRestrict_value (B : List Nat) (T : Tree) : (meterRestrict B T).value=restrict B T := by
 induction T with
 | leaf x => simp [meterRestrict,restrict]
 | node l r ihl ihr =>
  cases hl : restrict B l <;> cases hr : restrict B r <;> simp [meterRestrict,restrict,ihl,ihr,hl,hr]

theorem meterRestrict_bound (B : List Nat) (T : Tree) : (meterRestrict B T).work≤4*(B.length+2)*treeNodes T := by
 induction T with
 | leaf x => have h:=meterContains_bound x B;simp only [meterRestrict,treeNodes,Nat.mul_one];omega
 | node l r ihl ihr =>
  simp only [Nat.mul_add] at ihl ihr
  simp only [meterRestrict,treeNodes,Nat.mul_add,Nat.mul_one];omega

theorem restricted_nodes (B : List Nat) (T U : Tree) (restricted : restrict B T=some U) : treeNodes U≤treeNodes T := by
 induction T generalizing U with
 | leaf x =>
  simp only [restrict] at restricted
  split at restricted
  · cases restricted;exact Nat.le_refl _
  · contradiction
 | node l r ihl ihr =>
  cases hl : restrict B l <;> cases hr : restrict B r <;> simp only [restrict,hl,hr] at restricted
  · contradiction
  · cases restricted;have h:=ihr _ hr;simp only [treeNodes];omega
  · cases restricted;have h:=ihl _ hl;simp only [treeNodes];omega
  · cases restricted;have a:=ihl _ hl;have b:=ihr _ hr;simp only [treeNodes];omega

def meterRestrictionAgrees (T S : Tree) (B : List Nat) : Charged Bool :=
 let a:=meterRestrict B T;let b:=meterRestrict B S
 match a.value,b.value with
 | some u,some v=>let c:=meterSameShape u v;⟨c.value,a.work+b.work+c.work+4⟩
 | _,_=>⟨false,a.work+b.work+4⟩

@[simp] theorem meterRestrictionAgrees_value (T S : Tree) (B : List Nat) :
 (meterRestrictionAgrees T S B).value=restrictionAgrees T S B := by
 cases ht : restrict B T <;> cases hs : restrict B S <;>
  simp [meterRestrictionAgrees,restrictionAgrees,meterRestrict_value,ht,hs]

theorem meterRestrictionAgrees_bound (T S : Tree) (B : List Nat) (N : Nat)
 (tn : treeNodes T≤2*N) (sn : treeNodes S≤2*N) (bl : B.length≤N) :
 (meterRestrictionAgrees T S B).work≤128*(N+1)^2 := by
 have a:=meterRestrict_bound B T
 have b:=meterRestrict_bound B S
 have ea:=Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.add_le_add_right bl 2)) tn
 have eb:=Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.add_le_add_right bl 2)) sn
 cases hu : (meterRestrict B T).value with
 | none =>
  cases hv : (meterRestrict B S).value <;> simp only [meterRestrictionAgrees,hu,hv]
  all_goals simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm N 2] at a b ea eb ⊢
  all_goals omega
 | some u =>
  cases hv : (meterRestrict B S).value with
  | none =>
   simp only [meterRestrictionAgrees,hu,hv]
   simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm N 2] at a b ea eb ⊢
   omega
  | some v =>
   simp only [meterRestrictionAgrees,hu,hv]
   have un:=restricted_nodes B T u (by simpa only [meterRestrict_value] using hu)
   have vn:=restricted_nodes B S v (by simpa only [meterRestrict_value] using hv)
   have shape:=meterSameShape_bound u v
   have scaled:=Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.le_trans un tn)) (Nat.le_trans vn sn)
   simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm N 2] at a b ea eb shape scaled ⊢
   omega
end GenericForest.CheckCorrespondence
