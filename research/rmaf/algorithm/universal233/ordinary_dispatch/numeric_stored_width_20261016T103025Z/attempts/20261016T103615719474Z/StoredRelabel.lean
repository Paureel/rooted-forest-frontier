import StoredFreshPair
namespace OrdinaryDispatch.StoredNumeric
open RMAF Universal233.WholeSourceWork Universal233.CoreWork
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.CheckCorrespondence

def swapCopy (a b x : Bits) : Charged Bits :=
 let left:=copiedEqual x a;let right:=copiedEqual x b
 let out:=copyBits (if left.value then b else if right.value then a else x)
 ⟨out.value,left.work+right.work+out.work+8⟩

@[simp] theorem swapCopy_value (a b x : Bits) : decode (swapCopy a b x).value=
 OrdinaryCommonSplit.swap (decode a) (decode b) (decode x) := by
 simp [swapCopy,copyBits_value,copiedEqual_value,OrdinaryCommonSplit.swap]

theorem swapCopy_width (B : Nat) (a b x : Bits) (ha : a.length≤B) (hb : b.length≤B) (hx : x.length≤B) :
 (swapCopy a b x).value.length≤B := by
 simp only [swapCopy,copyBits_value]
 split
 · exact hb
 · split <;> assumption

theorem swapCopy_work (B : Nat) (a b x : Bits) (ha : a.length≤B) (hb : b.length≤B) (hx : x.length≤B) :
 (swapCopy a b x).work≤128*(B+1) := by
 have left:=copiedEqual_work B x a hx ha
 have right:=copiedEqual_work B x b hx hb
 have width : (if (copiedEqual x a).value then b else if (copiedEqual x b).value then a else x).length≤B := by
  split
  · exact hb
  · split <;> assumption
 simp only [swapCopy,copyBits_work]
 omega

def relabelSwap (a b : Bits) : GenericForest.BinaryProvider.Tree→Charged GenericForest.BinaryProvider.Tree
 | .leaf x=>let out:=swapCopy a b x;⟨.leaf out.value,out.work+4⟩
 | .node l r=>let left:=relabelSwap a b l;let right:=relabelSwap a b r
              ⟨.node left.value right.value,left.work+right.work+4⟩

@[simp] theorem relabelSwap_value (a b : Bits) (T : GenericForest.BinaryProvider.Tree) :
 treeValue (relabelSwap a b T).value=OrdinaryCommonSplit.relabel (OrdinaryCommonSplit.swap (decode a) (decode b)) (treeValue T) := by
 induction T <;> simp_all [relabelSwap,treeValue,OrdinaryCommonSplit.relabel,labelValue,swapCopy_value]

theorem relabelSwap_width (B : Nat) (a b : Bits) (T : GenericForest.BinaryProvider.Tree)
 (ha : a.length≤B) (hb : b.length≤B) (cap : TreeWidth B T) : TreeWidth B (relabelSwap a b T).value := by
 induction T with
 | leaf x=>
  have hx:=cap x (by simp [leavesBits])
  simp only [relabelSwap]
  intro y hy
  have eq:y=(swapCopy a b x).value:=by simpa only [leavesBits,List.mem_singleton] using hy
  subst y;exact swapCopy_width B a b x ha hb hx
 | node l r il ir=>
  have lc:=il (treeWidth_left B l r cap);have rc:=ir (treeWidth_right B l r cap)
  intro x hx
  simp only [relabelSwap,leavesBits,List.mem_append] at hx
  exact hx.elim (lc x) (rc x)

theorem relabelSwap_nodes (a b : Bits) (T : GenericForest.BinaryProvider.Tree) :
 treeNodes (treeValue (relabelSwap a b T).value)=treeNodes (treeValue T) := by
 induction T <;> simp_all [relabelSwap,treeValue,treeNodes]

theorem relabelSwap_work (B : Nat) (a b : Bits) (T : GenericForest.BinaryProvider.Tree)
 (ha : a.length≤B) (hb : b.length≤B) (cap : TreeWidth B T) :
 (relabelSwap a b T).work≤(128*(B+1)+4)*treeNodes (treeValue T) := by
 induction T with
 | leaf x=>
  have h:=swapCopy_work B a b x ha hb (cap x (by simp [leavesBits]))
  simp only [relabelSwap,treeValue,treeNodes,Nat.mul_one];omega
 | node l r il ir=>
  have lc:=il (treeWidth_left B l r cap);have rc:=ir (treeWidth_right B l r cap)
  simp only [relabelSwap,treeValue,treeNodes,Nat.mul_add,Nat.mul_one] at lc rc ⊢
  omega

/-- Concrete represented marked restriction. Selector cons, all comparisons,
copies and rebuilt tree constructors are included in the work field. -/
def markedBits (T : GenericForest.BinaryProvider.Tree) (X : Block) (y rho : Bits) : Charged (Option GenericForest.BinaryProvider.Tree) :=
 let restricted:=restrictLabels (y::X) T
 match restricted.value with
 | none=>⟨none,restricted.work+8⟩
 | some U=>let out:=relabelSwap y rho U;⟨some out.value,restricted.work+out.work+8⟩

@[simp] theorem markedBits_value (T : GenericForest.BinaryProvider.Tree) (X : Block) (y rho : Bits) :
 targetValue (markedBits T X y rho).value=OrdinaryCommonSplit.marked (treeValue T) (blockValue X) (decode y) (decode rho) := by
 have restricted:=GenericForest.BinaryProducer.restrictLabels_value (y::X) T
 unfold markedBits OrdinaryCommonSplit.marked
 simp only [blockValue,List.map_cons,labelValue] at restricted
 cases h : (restrictLabels (y::X) T).value with
 | none=>simp only [h,targetValue,Option.map_none] at restricted ⊢;rw [←restricted];rfl
 | some U=>
  simp only [h,targetValue,Option.map_some] at restricted ⊢
  rw [←restricted]
  simp only [Option.map_some,relabelSwap_value]

theorem markedBits_width (B : Nat) (T U : GenericForest.BinaryProvider.Tree) (X : Block) (y rho : Bits)
 (tc : TreeWidth B T) (hy : y.length≤B) (hr : rho.length≤B) (h : (markedBits T X y rho).value=some U) : TreeWidth B U := by
 unfold markedBits at h
 cases r : (restrictLabels (y::X) T).value with
 | none=>simp [r] at h
 | some V=>
  simp only [r,Option.some.injEq] at h
  subst U
  exact relabelSwap_width B y rho V hy hr (restrictedWidth B (y::X) T V tc r)

def markedFee (N P B : Nat) : Nat := GenericForest.ScalarBits.beta B*(4*(P+3)*N)+(128*(B+1)+4)*N+8

theorem markedBits_work (N P B : Nat) (T : GenericForest.BinaryProvider.Tree) (X : Block) (y rho : Bits)
 (tn : treeNodes (treeValue T)≤N) (xl : X.length≤P) (tc : TreeWidth B T)
 (xc : BlockWidth B X) (hy : y.length≤B) (hr : rho.length≤B) :
 (markedBits T X y rho).work≤markedFee N P B := by
 have selectors : BlockWidth B (y::X) := by
  intro x hx;rcases List.mem_cons.1 hx with rfl|hx
  · exact hy
  · exact xc x hx
 have restrictFee:=restrictLabels_projects B (y::X) T selectors tc
 have sourceFee:=meterRestrict_bound (blockValue (y::X)) (treeValue T)
 have costbound:=Nat.mul_le_mul (Nat.mul_le_mul_left 4 (show (blockValue (y::X)).length+2≤P+3 by simp only [blockValue_length,List.length_cons];omega)) tn
 have charge:=Nat.mul_le_mul_left (GenericForest.ScalarBits.beta B) costbound
 simp only [Projects] at restrictFee
 unfold markedBits
 cases h : (restrictLabels (y::X) T).value with
 | none=>simp only [h];unfold markedFee;omega
 | some U=>
  have wc:=restrictedWidth B (y::X) T U tc h
  have projection:=GenericForest.BinaryProducer.restrictLabels_value (y::X) T
  have original : restrict (blockValue (y::X)) (treeValue T)=some (treeValue U) := by simpa only [h,targetValue,Option.map_some] using projection.symm
  have node:=restricted_nodes _ _ _ original
  have fee:=relabelSwap_work B y rho U hy hr wc
  have bound:=Nat.mul_le_mul_left (128*(B+1)+4) (Nat.le_trans node tn)
  simp only [h];unfold markedFee;omega
end OrdinaryDispatch.StoredNumeric
