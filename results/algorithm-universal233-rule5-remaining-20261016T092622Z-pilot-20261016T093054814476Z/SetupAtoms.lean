import SelectedRestriction
import ProperPairWork
import BuildSetup
namespace Universal233.Rule5RemainingLocalWork
open RMAF CoreGraph HardParent CoreWork Rule5PrefixLocalWork Rule5PendantLocalWork
open GenericForest.CheckCorrespondence OrdinaryCommonSplit OrdinaryCommonSplit.Source

def bump {α : Type} (k : Nat) (r : Measured α) : Measured α := ⟨r.value,k+r.work⟩
@[simp] theorem bump_value {α : Type} (k : Nat) (r : Measured α) : (bump k r).value=r.value := rfl

def eraseMeter (x : Nat) : List Nat→Measured (List Nat)
 | []=>⟨[],1⟩
 | y::ys=>if x==y then ⟨ys,2⟩ else let r:=eraseMeter x ys;⟨y::r.value,r.work+3⟩

theorem erase_value (x : Nat) (xs : List Nat) : (eraseMeter x xs).value=xs.erase x := by
 induction xs with
 | nil=>rfl
 | cons y ys ih=>by_cases h:x=y <;> simp [eraseMeter,List.erase_cons,ih,h,Ne.symm h]

theorem erase_work (x : Nat) (xs : List Nat) : (eraseMeter x xs).work≤3*xs.length+1 := by
 induction xs with
 | nil=>simp [eraseMeter]
 | cons y ys ih=>simp only [eraseMeter];split <;> simp only [List.length_cons] <;> omega

/-- Literal isPerm decision underlying List.decidablePerm: contains, erase,
then recursive tail. Repeated membership/erase scans are separately billed. -/
def permMeter : List Nat→List Nat→Measured Bool
 | [],ys=>⟨ys.isEmpty,1⟩
 | x::xs,ys=>let c:=containsMeter x ys
              if c.value then let e:=eraseMeter x ys;let r:=permMeter xs e.value
                              ⟨r.value,c.work+e.work+r.work+2⟩
              else ⟨false,c.work+1⟩

theorem perm_value (xs ys : List Nat) : (permMeter xs ys).value=decide (xs.Perm ys) := by
 have aux (xs ys : List Nat) : (permMeter xs ys).value=xs.isPerm ys := by
  induction xs generalizing ys with
  | nil=>rfl
  | cons x xs ih=>simp only [permMeter,List.isPerm,contains_value,erase_value];split <;> simp_all
 apply Bool.eq_iff_iff.2
 simp only [aux,List.isPerm_iff,decide_eq_true_eq]

theorem perm_work (xs ys : List Nat) :
 (permMeter xs ys).work≤(5*ys.length+5)*(xs.length+1) := by
 induction xs generalizing ys with
 | nil=>simp [permMeter]
 | cons x xs ih=>
  have c:=contains_work x ys;have e:=erase_work x ys
  have r:=ih (eraseMeter x ys).value
  have short : (eraseMeter x ys).value.length≤ys.length := by rw [erase_value];exact List.length_erase_le
  have scale:=Nat.mul_le_mul_right (xs.length+1) (Nat.add_le_add_right (Nat.mul_le_mul_left 5 short) 5)
  simp only [permMeter,List.length_cons]
  have slot : (5*ys.length+5)*(xs.length+1+1)=(5*ys.length+5)*(xs.length+1)+(5*ys.length+5):=Nat.mul_succ _ _
  rw [slot];split <;> omega

def partitionTreeMeter (T : Tree) (X Y : List Nat) : Measured Bool :=
 let l:=leavesMeter T;let p:=meterPartition l.value [X,Y]
 ⟨p.value,l.work+p.work+3⟩

theorem partition_tree_value (T : Tree) (X Y : List Nat) :
 (partitionTreeMeter T X Y).value=partitionCheck (leaves T) [X,Y] := by
 simp only [partitionTreeMeter,meterPartition_value,leaves_value]

theorem partition_tree_work (T : Tree) (X Y : List Nat) (N : Nat)
 (ht : (leaves T).length≤N) (hxy : X.length+Y.length≤N) (two : 2≤N) :
 (partitionTreeMeter T X Y).work≤4*N*N+partitionCap N+3 := by
 have l:=leaves_work T
 have p:=meterPartition_bound (leaves T) [X,Y] N ht (by simpa) (by simpa using hxy)
 have scale:=Nat.mul_le_mul_left 4 (Nat.mul_le_mul ht ht)
 simp only [partitionTreeMeter,leaves_value]
 simp only [Nat.mul_assoc] at l scale ⊢;omega

def maxMeter : List Nat→Measured Nat
 | []=>⟨0,1⟩
 | x::xs=>let r:=maxMeter xs;⟨max x r.value,r.work+3⟩

theorem max_value (xs : List Nat) : (maxMeter xs).value=labelMax xs := by
 induction xs <;> simp_all [maxMeter,labelMax]

theorem max_work (xs : List Nat) : (maxMeter xs).work=3*xs.length+1 := by
 induction xs <;> simp_all [maxMeter] <;> omega

/-- relabel recursively copies every node; swap pays both scalar tests. -/
def relabelMeter (y rho : Nat) : Tree→Measured Tree
 | .leaf x=>⟨.leaf (RestrictionBridge.swap y rho x),4⟩
 | .node l r=>let a:=relabelMeter y rho l;let b:=relabelMeter y rho r
               ⟨.node a.value b.value,a.work+b.work+2⟩

theorem relabel_value (y rho : Nat) (T : Tree) :
 (relabelMeter y rho T).value=RestrictionBridge.relabel (RestrictionBridge.swap y rho) T := by
 induction T <;> simp_all [relabelMeter,RestrictionBridge.relabel]

theorem relabel_work (y rho : Nat) (T : Tree) : (relabelMeter y rho T).work≤4*treeNodes T := by
 induction T <;> simp_all [relabelMeter,treeNodes] <;> omega

def markedMeter (T : Tree) (X : List Nat) (y rho : Nat) : Measured (Option Tree) :=
 let r:=meterRestrict (y::X) T
 match r.value with
 | none=>⟨none,r.work+2⟩
 | some U=>let a:=relabelMeter y rho U;⟨some a.value,r.work+a.work+3⟩

theorem marked_value (T : Tree) (X : List Nat) (y rho : Nat) :
 (markedMeter T X y rho).value=marked T X y rho := by
 simp only [markedMeter,marked,meterRestrict_value]
 cases h:restrict (y::X) T <;> simp [h,relabel_value]

theorem marked_work (T : Tree) (X : List Nat) (y rho : Nat) :
 (markedMeter T X y rho).work≤(4*(X.length+3)+4)*treeNodes T+3 := by
 have r:=meterRestrict_bound (y::X) T
 simp only [List.length_cons] at r
 cases h:(meterRestrict (y::X) T).value with
 | none=>simp only [markedMeter,h];simp only [Nat.add_mul];omega
 | some U=>
  have un:=restricted_nodes (y::X) T U (by simpa only [meterRestrict_value] using h)
  have a:=relabel_work y rho U;have sc:=Nat.mul_le_mul_left 4 un
  simp only [markedMeter,h,Nat.add_mul];omega
end Universal233.Rule5RemainingLocalWork
