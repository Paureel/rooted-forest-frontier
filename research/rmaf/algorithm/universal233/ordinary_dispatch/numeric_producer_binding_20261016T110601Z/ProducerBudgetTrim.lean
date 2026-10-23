import StoredBudget
import ProducerRawBinding
namespace OrdinaryDispatch.StoredNumeric.ProducerBinding
open GenericForest.ScalarBits GenericForest.BinaryProvider Universal233.WholeSourceWork

/-- Little-endian high-zero trim. Every inspected bit, branch and rebuilt cell
is charged; the empty representation is canonical zero. -/
def trimBudget : Bits → Charged Bits
 | [] => ⟨[],1⟩
 | b::bs =>
  let r:=trimBudget bs
  match r.value with
  | [] => ⟨if b then [true] else [],r.work+8⟩
  | c::cs => ⟨b::c::cs,r.work+8⟩

@[simp] theorem trimBudget_value (q : Bits) : decode (trimBudget q).value=decode q := by
 induction q with
 | nil=>rfl
 | cons b bs ih=>
  cases h : (trimBudget bs).value with
  | nil=>cases b <;> simp [trimBudget,h,decode,bit] at ih ⊢ <;> omega
  | cons c cs=>simp only [h,decode] at ih;simp [trimBudget,h,decode,ih]

@[simp] theorem trimBudget_work (q : Bits) : (trimBudget q).work=8*q.length+1 := by
 induction q with
 | nil=>rfl
 | cons b bs ih=>cases h : (trimBudget bs).value <;> simp [trimBudget,h,ih] <;> omega

theorem trimBudget_length (q : Bits) : (trimBudget q).value.length≤q.length := by
 induction q with
 | nil=>simp [trimBudget]
 | cons b bs ih=>
  cases h : (trimBudget bs).value with
  | nil=>cases b <;> simp [trimBudget,h]
  | cons c cs=>simp only [h,List.length_cons] at ih;simp only [trimBudget,h,List.length_cons];omega

/-- A deliberately conservative semantic width bound, independent of padding.
This is a theorem about the output of this executable trim, not input policy. -/
theorem trimBudget_semantic_width (q : Bits) : (trimBudget q).value.length≤decode q := by
 induction q with
 | nil=>simp [trimBudget,decode]
 | cons b bs ih=>
  have v:=trimBudget_value bs
  cases h : (trimBudget bs).value with
  | nil=>cases b <;> simp [trimBudget,h,decode,bit]
  | cons c cs=>
   simp only [h,List.length_cons] at ih
   cases b <;> simp only [trimBudget,h,List.length_cons,decode,bit,Bool.false_eq_true,ite_false,ite_true] <;> omega

/-- Normalization of an already paid budget operation retains its full bill. -/
def finishBudget (op : Charged Bits) : Charged Bits :=
 let t:=trimBudget op.value
 ⟨t.value,op.work+t.work+4⟩
@[simp] theorem finishBudget_value (op : Charged Bits) : decode (finishBudget op).value=decode op.value := trimBudget_value _
@[simp] theorem finishBudget_work (op : Charged Bits) : (finishBudget op).work=op.work+8*op.value.length+5 := by simp [finishBudget];omega
theorem finishBudget_width (op : Charged Bits) : (finishBudget op).value.length≤decode op.value := trimBudget_semantic_width _

def subtractCanonical (q d : Bits) : Charged Bits := finishBudget (subtractBits q d)
@[simp] theorem subtractCanonical_value (q d : Bits) : decode (subtractCanonical q d).value=decode q-decode d := by simp [subtractCanonical]
theorem subtractCanonical_width (q d : Bits) : (subtractCanonical q d).value.length≤decode q := by
 have h:=finishBudget_width (subtractBits q d);simp only [subtractBits_value] at h;dsimp only [subtractCanonical];omega

def allocationCanonical (q k p : Bits) : Charged Bits := finishBudget (GenericForest.BinaryProducer.allocationBits q k p)
@[simp] theorem allocationCanonical_value (q k p : Bits) :
 decode (allocationCanonical q k p).value=decode q-decode k-2*(decode p-1) := by simp [allocationCanonical]
theorem allocationCanonical_width (q k p : Bits) : (allocationCanonical q k p).value.length≤decode q := by
 have h:=finishBudget_width (GenericForest.BinaryProducer.allocationBits q k p)
 simp only [GenericForest.BinaryProducer.allocationBits_value] at h
 dsimp only [allocationCanonical];omega
end OrdinaryDispatch.StoredNumeric.ProducerBinding
