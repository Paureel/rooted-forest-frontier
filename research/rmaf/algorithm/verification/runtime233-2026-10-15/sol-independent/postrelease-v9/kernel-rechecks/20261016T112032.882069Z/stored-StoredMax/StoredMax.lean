import StoredPrecontrols
namespace OrdinaryDispatch.StoredNumeric
open RMAF Universal233.WholeSourceWork Universal233.CoreWork
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.CheckCorrespondence

/-- Finite-bit comparison followed by an actual copy of the chosen array. A
numeric tie chooses the right operand, preserving its existing padding. -/
def maximumCopy (x y : Bits) : Charged Bits :=
 let order:=compareBits x y
 let out:=copyBits (if order.value=.greater then x else y)
 ⟨out.value,order.work+out.work+4⟩

@[simp] theorem maximumCopy_value (x y : Bits) :
 decode (maximumCopy x y).value=max (decode x) (decode y) := by
 have h:=compareBits_spec x y
 cases hr : (compareBits x y).value <;> simp only [hr,OrderSpec] at h <;>
  simp [maximumCopy,hr,copyBits_value] <;> omega

theorem maximumCopy_width (x y : Bits) : (maximumCopy x y).value.length≤max x.length y.length := by
 simp only [maximumCopy,copyBits_value]
 split
 · exact Nat.le_max_left _ _
 · exact Nat.le_max_right _ _

theorem maximumCopy_work (B : Nat) (x y : Bits) (hx : x.length≤B) (hy : y.length≤B) :
 (maximumCopy x y).work≤24*(B+1) := by
 have cmp:=compareBits_work x y
 have width : (if (compareBits x y).value=.greater then x else y).length≤B := by split <;> assumption
 simp only [maximumCopy,copyBits_work]
 omega

/-- Literal fold-right maximum over represented labels. Empty input uses the
empty zero array; all nonempty winners are explicitly copied. -/
def maximumBlock : Block→Charged Bits
 | []=>⟨[],1⟩
 | x::xs=>let tail:=maximumBlock xs;let out:=maximumCopy x tail.value
           ⟨out.value,tail.work+out.work+4⟩

@[simp] theorem maximumBlock_value (xs : Block) :
 decode (maximumBlock xs).value=OrdinaryCommonSplit.Source.labelMax (blockValue xs) := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>simp only [maximumBlock,maximumCopy_value,ih,blockValue,List.map_cons,OrdinaryCommonSplit.Source.labelMax,List.foldr_cons,labelValue]

theorem maximumBlock_width (B : Nat) (xs : Block) (cap : BlockWidth B xs) :
 (maximumBlock xs).value.length≤B := by
 induction xs with
 | nil=>simp [maximumBlock]
 | cons x xs ih=>
  have head:=cap x (by simp)
  have tail:=ih (fun y hy=>cap y (by simp [hy]))
  have width:=maximumCopy_width x (maximumBlock xs).value
  simp only [maximumBlock]
  exact Nat.le_trans width (Nat.max_le.mpr ⟨head,tail⟩)

theorem maximumBlock_work (B : Nat) (xs : Block) (cap : BlockWidth B xs) :
 (maximumBlock xs).work≤32*(B+1)*(xs.length+1) := by
 induction xs with
 | nil=>simp only [maximumBlock,List.length_nil,Nat.zero_add,Nat.mul_one];omega
 | cons x xs ih=>
  have tc : BlockWidth B xs:=fun y hy=>cap y (by simp [hy])
  have tail:=ih tc
  have maxfee:=maximumCopy_work B x (maximumBlock xs).value (cap x (by simp)) (maximumBlock_width B xs tc)
  simp only [maximumBlock,List.length_cons,Nat.mul_add,Nat.mul_one] at *
  omega

theorem successor_width (x : Bits) : (incrementBits x).value.length≤x.length+1 := by
 simpa only [incrementBits,List.length_nil,Nat.max_zero] using addCarry_length x [] true

theorem successor_work (x : Bits) : (incrementBits x).work≤12*(x.length+1) := by
 simpa only [incrementBits,List.length_nil,Nat.add_zero] using addCarry_work x [] true

def freshOne (T : GenericForest.BinaryProvider.Tree) : Charged Bits :=
 let labels:=leavesCopy T
 let maximum:=maximumBlock labels.value
 let fresh:=incrementBits maximum.value
 let out:=copyBits fresh.value
 ⟨out.value,labels.work+maximum.work+fresh.work+out.work+8⟩

@[simp] theorem freshOne_value (T : GenericForest.BinaryProvider.Tree) :
 decode (freshOne T).value=OrdinaryDispatch.commonFresh (treeValue T) := by
 simp only [freshOne,copyBits_value,incrementBits_value,maximumBlock_value,leavesCopy_value,leaves_projection,OrdinaryDispatch.commonFresh]

theorem freshOne_width (B : Nat) (T : GenericForest.BinaryProvider.Tree) (cap : TreeWidth B T) :
 (freshOne T).value.length≤B+1 := by
 have max:=maximumBlock_width B (leavesBits T) cap
 have inc:=successor_width (maximumBlock (leavesBits T)).value
 simp only [freshOne,copyBits_value,leavesCopy_value]
 omega

/-- Polynomial in stored width B and source node cap N. -/
def freshOneFee (N B : Nat) : Nat :=
 GenericForest.ScalarBits.beta B*(8*(N+1)^2)+32*(B+1)*(N+1)+12*(B+1)+4*(B+1)+9

theorem freshOne_work (N B : Nat) (T : GenericForest.BinaryProvider.Tree)
 (nodes : treeNodes (treeValue T)≤N) (cap : TreeWidth B T) : (freshOne T).work≤freshOneFee N B := by
 have labels:=leavesCopy_projects T B cap
 have scalar:=meterLeaves_cap (treeValue T) N nodes
 have paid:=Nat.mul_le_mul_left (GenericForest.ScalarBits.beta B) scalar
 have leaf:=leaves_nodes (treeValue T)
 have size : (leavesBits T).length≤N := by rw [←blockValue_length,leaves_projection];omega
 have maximum:=maximumBlock_work B (leavesBits T) cap
 have maxwidth:=maximumBlock_width B (leavesBits T) cap
 have inc:=successor_work (maximumBlock (leavesBits T)).value
 have out:=successor_width (maximumBlock (leavesBits T)).value
 have scale:=Nat.mul_le_mul_left (32*(B+1)) (Nat.add_le_add_right size 1)
 simp only [Projects] at labels
 simp only [freshOne,freshOneFee,leavesCopy_value,copyBits_work]
 omega
end OrdinaryDispatch.StoredNumeric
