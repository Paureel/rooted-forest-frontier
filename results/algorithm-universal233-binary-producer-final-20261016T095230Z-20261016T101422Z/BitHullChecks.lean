import BitTreeChecks
namespace GenericForest.ScalarBits
open RMAF Universal233 Universal233.WholeSourceWork GenericForest.CheckCorrespondence

def bitRooted (W : Nat) (D : List Nat) : Tree→Charged (List RMAF.Vertex)
 | .leaf x=>let m:=bitContains W x D;⟨if m.value then [[]] else [],m.work+8*beta W⟩
 | .node l r=>let a:=bitRooted W D l;let b:=bitRooted W D r
               ⟨if a.value.isEmpty&&b.value.isEmpty then [] else []::(prependSide false a.value++prependSide true b.value),
                a.work+b.work+8*beta W*(a.value.length+b.value.length+2)⟩

theorem bitRooted_refines (W : Nat) (D : List Nat) (T : Tree) (dc : LabelCap W D) (tc : TreeCap W T) :
 Refines W (bitRooted W D T) (meterRooted D T) := by
 induction T with
 | leaf x=>
  have m:=bitContains_refines W x D (tc x (by simp [leaves])) dc
  simp only [Refines] at m ⊢
  simp only [bitRooted,meterRooted,m.1]
  refine ⟨by trivial,?_⟩
  simp only [Nat.mul_add,Nat.mul_comm (beta W) 8];omega
 | node l r ihl ihr=>
  have a:=ihl (treeCap_left W l r tc);have b:=ihr (treeCap_right W l r tc)
  simp only [Refines] at a b ⊢
  simp only [bitRooted,meterRooted,a.1,b.1]
  refine ⟨by trivial,?_⟩
  simp only [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm (beta W) 8];omega

def bitMinimal (W : Nat) (D : List Nat) : Tree→Charged (List RMAF.Vertex)
 | .leaf x=>let m:=bitContains W x D;⟨if m.value then [[]] else [],m.work+8*beta W⟩
 | .node l r=>
  let a:=bitRooted W D l;let b:=bitRooted W D r
  if a.value.isEmpty then let m:=bitMinimal W D r
   ⟨prependSide true m.value,a.work+b.work+m.work+8*beta W*(m.value.length+2)⟩
  else if b.value.isEmpty then let m:=bitMinimal W D l
   ⟨prependSide false m.value,a.work+b.work+m.work+8*beta W*(m.value.length+2)⟩
  else ⟨[]::(prependSide false a.value++prependSide true b.value),a.work+b.work+8*beta W*(a.value.length+b.value.length+2)⟩

theorem bitMinimal_refines (W : Nat) (D : List Nat) (T : Tree) (dc : LabelCap W D) (tc : TreeCap W T) :
 Refines W (bitMinimal W D T) (meterMinimal D T) := by
 induction T with
 | leaf x=>
  have m:=bitContains_refines W x D (tc x (by simp [leaves])) dc
  simp only [Refines] at m ⊢
  simp only [bitMinimal,meterMinimal,m.1]
  refine ⟨by trivial,?_⟩
  simp only [Nat.mul_add,Nat.mul_comm (beta W) 8];omega
 | node l r ihl ihr=>
  have lc:=treeCap_left W l r tc;have rc:=treeCap_right W l r tc
  have a:=bitRooted_refines W D l dc lc;have b:=bitRooted_refines W D r dc rc
  have ml:=ihl lc;have mr:=ihr rc
  simp only [Refines] at a b ml mr ⊢
  simp only [bitMinimal,meterMinimal,a.1,b.1]
  split
  · simp only [mr.1]
    refine ⟨by trivial,?_⟩
    simp only [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm (beta W) 8];omega
  · split
    · simp only [ml.1]
      refine ⟨by trivial,?_⟩
      simp only [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm (beta W) 8];omega
    · refine ⟨by trivial,?_⟩
      simp only [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm (beta W) 8];omega

def bitHullPair (W : Nat) (T : Tree) (B C : List Nat) : Charged Bool :=
 let a:=bitMinimal W B T;let b:=bitMinimal W C T;let d:=pointerLift W (meterDisjoint a.value b.value)
 ⟨d.value,a.work+b.work+d.work+2*beta W⟩

theorem bitHullPair_refines (W : Nat) (T : Tree) (B C : List Nat)
 (tc : TreeCap W T) (bc : LabelCap W B) (cc : LabelCap W C) :
 Refines W (bitHullPair W T B C) (meterHullPair T B C) := by
 have a:=bitMinimal_refines W B T bc tc;have b:=bitMinimal_refines W C T cc tc
 simp only [Refines] at a b ⊢
 simp only [bitHullPair,meterHullPair,pointerLift,a.1,b.1]
 refine ⟨by trivial,?_⟩
 simp only [Nat.mul_add,Nat.mul_comm (beta W) 2];omega

def bitPairwise (W : Nat) (T : Tree) : Forest→Charged Bool
 | []=>⟨true,beta W⟩
 | B::F=>let a:=bitAll W (bitHullPair W T B) F;let r:=bitPairwise W T F
          ⟨a.value&&r.value,a.work+r.work+4*beta W⟩

theorem bitPairwise_refines (W : Nat) (T : Tree) (F : Forest)
 (tc : TreeCap W T) (blocks : ∀B∈F,LabelCap W B) :
 Refines W (bitPairwise W T F) (meterPairwise T F) := by
 induction F with
 | nil=>simp [Refines,bitPairwise,meterPairwise]
 | cons B F ih=>
  have a:=bitAll_refines W (bitHullPair W T B) (meterHullPair T B) F
   (fun C hc=>bitHullPair_refines W T B C tc (blocks B (by simp)) (blocks C (by simp [hc])))
  have r:=ih (fun C hc=>blocks C (by simp [hc]))
  simp only [Refines] at a r ⊢
  simp only [bitPairwise,meterPairwise,a.1,r.1]
  refine ⟨by trivial,?_⟩
  simp only [Nat.mul_add,Nat.mul_comm (beta W) 4];omega
end GenericForest.ScalarBits
