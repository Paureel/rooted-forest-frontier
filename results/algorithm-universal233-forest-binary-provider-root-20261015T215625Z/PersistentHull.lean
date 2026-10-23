import PersistentCapacity
namespace GenericForest.BinaryProvider
open Universal233.WholeSourceWork GenericForest.ScalarBits GenericForest.CheckCorrespondence
abbrev Addresses:=List RMAF.Vertex

def appendSpine {α : Type} : List α→List α→Charged (List α)
 | [],ys=>⟨ys,1⟩
 | x::xs,ys=>let r:=appendSpine xs ys;⟨x::r.value,r.work+4⟩
@[simp] theorem appendSpine_value {α : Type} (xs ys : List α) : (appendSpine xs ys).value=xs++ys := by
 induction xs <;> simp_all [appendSpine]
@[simp] theorem appendSpine_work {α : Type} (xs ys : List α) : (appendSpine xs ys).work=4*xs.length+1 := by
 induction xs <;> simp only [appendSpine,List.length_nil,List.length_cons] at * <;> omega

/-- Each address keeps its original tail; allocating a side bit and outer cons
costs eight source operations. The unary original-tree paths are retained. -/
def prependAddresses (side : Bool) : Addresses→Charged Addresses
 | []=>⟨[],1⟩
 | v::vs=>let r:=prependAddresses side vs;⟨(side::v)::r.value,r.work+8⟩
@[simp] theorem prependAddresses_value (side : Bool) (A : Addresses) :
 (prependAddresses side A).value=RMAF.prependSide side A := by
 induction A <;> simp_all [prependAddresses,RMAF.prependSide]
@[simp] theorem prependAddresses_work (side : Bool) (A : Addresses) :
 (prependAddresses side A).work=8*A.length+1 := by
 induction A <;> simp only [prependAddresses,List.length_nil,List.length_cons] at * <;> omega

def joinAddresses (A B : Addresses) : Charged Addresses:=
 let a:=prependAddresses false A;let b:=prependAddresses true B;let c:=appendSpine a.value b.value
 ⟨[]::c.value,a.work+b.work+c.work+4⟩
@[simp] theorem joinAddresses_value (A B : Addresses) :
 (joinAddresses A B).value=[]::(RMAF.prependSide false A++RMAF.prependSide true B) := by simp [joinAddresses]
theorem joinAddresses_work (A B : Addresses) :
 (joinAddresses A B).work+8≤2*(8*(A.length+B.length+2)) := by
 simp only [joinAddresses,prependAddresses_work,appendSpine_work,prependAddresses_value,RMAF.prependSide,List.length_map];omega
 theorem beta_two (W : Nat) : 2≤ScalarBits.beta W:=by unfold ScalarBits.beta;omega

def rootedLabels (B : Block) : Tree→Charged Addresses
 | .leaf x=>let m:=containsLabel x B;⟨if m.value then [[]] else [],m.work+8⟩
 | .node l r=>let a:=rootedLabels B l;let b:=rootedLabels B r
               if a.value.isEmpty&&b.value.isEmpty then ⟨[],a.work+b.work+8⟩ else
                let j:=joinAddresses a.value b.value;⟨j.value,a.work+b.work+j.work+8⟩

theorem rootedLabels_projects (W : Nat) (B : Block) (T : Tree) (bc : BlockWidth W B) (tc : TreeWidth W T) :
 Projects W id (rootedLabels B T) (meterRooted (blockValue B) (treeValue T)) := by
 have p:=beta_positive W
 induction T with
 | leaf x=>
  have m:=containsLabel_projects W x B (tc x (by simp [leavesBits])) bc
  simp only [Projects,id_eq] at m ⊢
  simp only [rootedLabels,treeValue,meterRooted,m.1]
  constructor
  · trivial
  · simp only [Nat.mul_add];omega
 | node l r ihl ihr=>
  have a:=ihl (treeWidth_left W l r tc);have b:=ihr (treeWidth_right W l r tc)
  have j:=joinAddresses_work (rootedLabels B l).value (rootedLabels B r).value
  have k:=Nat.mul_le_mul_right (8*((rootedLabels B l).value.length+(rootedLabels B r).value.length+2)) (beta_two W)
  simp only [Projects,id_eq] at a b ⊢
  simp only [rootedLabels,treeValue,meterRooted,←a.1,←b.1]
  split
  · constructor
    · simp_all
    · simp only [Nat.mul_add,Nat.mul_one] at k ⊢;omega
  · constructor
    · simp_all only [Bool.not_eq_true,ite_false,joinAddresses_value]
    · simp only [Nat.mul_add,Nat.mul_one] at k ⊢;omega

def minimalLabels (B : Block) : Tree→Charged Addresses
 | .leaf x=>let m:=containsLabel x B;⟨if m.value then [[]] else [],m.work+8⟩
 | .node l r=>let a:=rootedLabels B l;let b:=rootedLabels B r
               if a.value.isEmpty then
                let m:=minimalLabels B r;let p:=prependAddresses true m.value
                ⟨p.value,a.work+b.work+m.work+p.work+8⟩
               else if b.value.isEmpty then
                let m:=minimalLabels B l;let p:=prependAddresses false m.value
                ⟨p.value,a.work+b.work+m.work+p.work+8⟩
               else let j:=joinAddresses a.value b.value;⟨j.value,a.work+b.work+j.work+8⟩

theorem minimalLabels_projects (W : Nat) (B : Block) (T : Tree) (bc : BlockWidth W B) (tc : TreeWidth W T) :
 Projects W id (minimalLabels B T) (meterMinimal (blockValue B) (treeValue T)) := by
 have p:=beta_positive W
 induction T with
 | leaf x=>
  have m:=containsLabel_projects W x B (tc x (by simp [leavesBits])) bc
  simp only [Projects,id_eq] at m ⊢
  simp only [minimalLabels,treeValue,meterMinimal,m.1]
  constructor
  · trivial
  · simp only [Nat.mul_add];omega
 | node l r ihl ihr=>
  have a:=rootedLabels_projects W B l bc (treeWidth_left W l r tc)
  have b:=rootedLabels_projects W B r bc (treeWidth_right W l r tc)
  have ml:=ihl (treeWidth_left W l r tc);have mr:=ihr (treeWidth_right W l r tc)
  have j:=joinAddresses_work (rootedLabels B l).value (rootedLabels B r).value
  have k:=Nat.mul_le_mul_right (8*((rootedLabels B l).value.length+(rootedLabels B r).value.length+2)) (beta_two W)
  simp only [Projects,id_eq] at a b ml mr ⊢
  simp only [minimalLabels,treeValue,meterMinimal,←a.1,←b.1]
  split
  · constructor
    · simp only [prependAddresses_value,mr.1]
    · have k:=Nat.mul_le_mul_right (8*((minimalLabels B r).value.length+2)) p
      simp only [prependAddresses_work,←mr.1,Nat.mul_add,Nat.mul_one] at k ⊢;omega
  · split
    · constructor
      · simp only [prependAddresses_value,ml.1]
      · have k:=Nat.mul_le_mul_right (8*((minimalLabels B l).value.length+2)) p
        simp only [prependAddresses_work,←ml.1,Nat.mul_add,Nat.mul_one] at k ⊢;omega
    · constructor
      · exact joinAddresses_value _ _
      · simp only [Nat.mul_add,Nat.mul_one] at k ⊢;omega
end GenericForest.BinaryProvider
