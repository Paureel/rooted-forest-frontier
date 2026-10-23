import StoredRelabel
namespace OrdinaryDispatch.StoredNumeric
open RMAF Universal233.WholeSourceWork Universal233.CoreWork
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.CheckCorrespondence

theorem treeWidth_mono {B W : Nat} {T : GenericForest.BinaryProvider.Tree}
 (cap : TreeWidth B T) (h : B≤W) : TreeWidth W T := fun x hx=>Nat.le_trans (cap x hx) h

def leafEqual (a : Bits) : GenericForest.BinaryProvider.Tree→Charged Bool
 | .leaf x=>let out:=copiedEqual x a;⟨out.value,out.work+2⟩
 | .node _ _=>⟨false,2⟩

@[simp] theorem leafEqual_value (a : Bits) (T : GenericForest.BinaryProvider.Tree) :
 (leafEqual a T).value=(treeValue T==RMAF.Tree.leaf (decode a)) := by
 cases T with
 | leaf x=>
  simp only [leafEqual,treeValue,copiedEqual_value,labelValue]
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq,RMAF.Tree.leaf.injEq]
 | node l r=>rfl

theorem leafEqual_work (B : Nat) (a : Bits) (T : GenericForest.BinaryProvider.Tree)
 (ha : a.length≤B) (cap : TreeWidth B T) : (leafEqual a T).work≤64*(B+1) := by
 cases T with
 | leaf x=>have h:=copiedEqual_work B x a (cap x (by simp [leavesBits])) ha;simp only [leafEqual];omega
 | node l r=>simp only [leafEqual];omega

/-- Both cherry orientations use copied finite-bit equality. All retained
leaves, new marker arrays and tree constructors are explicitly copied/charged. -/
def contractBits (a b z : Bits) : GenericForest.BinaryProvider.Tree→Charged GenericForest.BinaryProvider.Tree
 | .leaf x=>let out:=copyBits x;⟨.leaf out.value,out.work+4⟩
 | .node l r=>
   let la:=leafEqual a l;let rb:=leafEqual b r;let lb:=leafEqual b l;let ra:=leafEqual a r
   if (la.value&&rb.value)||(lb.value&&ra.value) then
    let out:=copyBits z;⟨.leaf out.value,la.work+rb.work+lb.work+ra.work+out.work+8⟩
   else
    let left:=contractBits a b z l;let right:=contractBits a b z r
    ⟨.node left.value right.value,la.work+rb.work+lb.work+ra.work+left.work+right.work+8⟩

@[simp] theorem contractBits_value (a b z : Bits) (T : GenericForest.BinaryProvider.Tree) :
 treeValue (contractBits a b z T).value=ForestState.contract (decode a) (decode b) (decode z) (treeValue T) := by
 induction T with
 | leaf x=>simp [contractBits,treeValue,ForestState.contract,copyBits_value]
 | node l r il ir=>simp only [contractBits,leafEqual_value,treeValue,ForestState.contract];split <;> simp_all [copyBits_value,treeValue,labelValue]

theorem contractBits_width (B : Nat) (a b z : Bits) (T : GenericForest.BinaryProvider.Tree)
 (hz : z.length≤B) (cap : TreeWidth B T) : TreeWidth B (contractBits a b z T).value := by
 induction T with
 | leaf x=>simpa only [contractBits,copyBits_value] using cap
 | node l r il ir=>
  simp only [contractBits]
  split
  · intro x hx
    have eq:x=z:=by simpa only [leavesBits,copyBits_value,List.mem_singleton] using hx
    subst x;exact hz
  · have lc:=il (treeWidth_left B l r cap);have rc:=ir (treeWidth_right B l r cap)
    intro x hx
    rcases List.mem_append.1 hx with h|h
    · exact lc x h
    · exact rc x h

theorem contractBits_nodes (a b z : Bits) (T : GenericForest.BinaryProvider.Tree) :
 treeNodes (treeValue (contractBits a b z T).value)≤treeNodes (treeValue T) := by
 induction T with
 | leaf x=>simp [contractBits,treeValue,treeNodes]
 | node l r il ir=>simp only [contractBits];split <;> simp only [treeValue,treeNodes] <;> omega

theorem contractBits_work (B : Nat) (a b z : Bits) (T : GenericForest.BinaryProvider.Tree)
 (ha : a.length≤B) (hb : b.length≤B) (hz : z.length≤B) (cap : TreeWidth B T) :
 (contractBits a b z T).work≤400*(B+1)*treeNodes (treeValue T) := by
 induction T with
 | leaf x=>
  have hx:=cap x (by simp [leavesBits])
  change x.length≤B at hx
  simp only [contractBits,copyBits_work,treeValue,treeNodes,Nat.mul_one];omega
 | node l r il ir=>
  have lc:=treeWidth_left B l r cap;have rc:=treeWidth_right B l r cap
  have la:=leafEqual_work B a l ha lc;have rb:=leafEqual_work B b r hb rc
  have lb:=leafEqual_work B b l hb lc;have ra:=leafEqual_work B a r ha rc
  have left:=il lc;have right:=ir rc
  simp only [contractBits]
  split
  · have positive : 1≤treeNodes (treeValue (.node l r)):=treeNodes_pos _
    have scaled:=Nat.mul_le_mul_left (400*(B+1)) positive
    simp only [copyBits_work,Nat.mul_one] at scaled ⊢
    omega
  · simp only [treeValue,treeNodes,Nat.mul_add,Nat.mul_one] at left right ⊢;omega

/-- Exact represented operands at CommonDispatch.runCommonCherry's direct call.
The caller may exchange T/S before invoking this routine. -/
def contractPairBits (a b : Bits) (T S : GenericForest.BinaryProvider.Tree) :
 Charged (GenericForest.BinaryProvider.Tree×GenericForest.BinaryProvider.Tree) :=
 let z:=freshOne T
 let left:=contractBits a b z.value T;let right:=contractBits a b z.value S
 ⟨(left.value,right.value),z.work+left.work+right.work+8⟩

@[simp] theorem contractPairBits_value (a b : Bits) (T S : GenericForest.BinaryProvider.Tree) :
 treeValue (contractPairBits a b T S).value.1=
 ForestState.contract (decode a) (decode b) (OrdinaryDispatch.commonFresh (treeValue T)) (treeValue T) ∧
 treeValue (contractPairBits a b T S).value.2=
 ForestState.contract (decode a) (decode b) (OrdinaryDispatch.commonFresh (treeValue T)) (treeValue S) := by
 simp [contractPairBits,contractBits_value,freshOne_value]

theorem contractPairBits_width (B : Nat) (a b : Bits) (T S : GenericForest.BinaryProvider.Tree)
 (tc : TreeWidth B T) (sc : TreeWidth B S) :
 TreeWidth (B+1) (contractPairBits a b T S).value.1 ∧ TreeWidth (B+1) (contractPairBits a b T S).value.2 := by
 have fresh:=freshOne_width B T tc
 exact ⟨contractBits_width (B+1) a b _ T fresh (treeWidth_mono tc (by omega)),
  contractBits_width (B+1) a b _ S fresh (treeWidth_mono sc (by omega))⟩

def contractPairFee (N B : Nat) : Nat := freshOneFee N B+2*(400*(B+2)*N)+8

theorem contractPairBits_work (N B : Nat) (a b : Bits) (T S : GenericForest.BinaryProvider.Tree)
 (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N)
 (ha : a.length≤B) (hb : b.length≤B) (tc : TreeWidth B T) (sc : TreeWidth B S) :
 (contractPairBits a b T S).work≤contractPairFee N B := by
 have fresh:=freshOne_width B T tc;have ff:=freshOne_work N B T tn tc
 have l:=contractBits_work (B+1) a b (freshOne T).value T (by omega) (by omega) fresh (treeWidth_mono tc (by omega))
 have r:=contractBits_work (B+1) a b (freshOne T).value S (by omega) (by omega) fresh (treeWidth_mono sc (by omega))
 have lt:=Nat.mul_le_mul_left (400*(B+2)) tn;have rt:=Nat.mul_le_mul_left (400*(B+2)) sn
 have ll : (contractBits a b (freshOne T).value T).work≤400*(B+2)*treeNodes (treeValue T) := by simpa only [Nat.add_assoc,Nat.reduceAdd] using l
 have rr : (contractBits a b (freshOne T).value S).work≤400*(B+2)*treeNodes (treeValue S) := by simpa only [Nat.add_assoc,Nat.reduceAdd] using r
 simp only [contractPairBits,contractPairFee]
 omega
end OrdinaryDispatch.StoredNumeric
