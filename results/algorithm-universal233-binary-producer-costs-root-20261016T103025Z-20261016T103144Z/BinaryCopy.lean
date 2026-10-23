import BinaryCounters
namespace GenericForest.ScalarBits
open Universal233.WholeSourceWork

/-- Explicit reference copy of a supplied bit array; no native Nat conversion. -/
def copyBits : List Bool→Charged (List Bool)
 | []=>⟨[],1⟩
 | b::bs=>let r:=copyBits bs;⟨b::r.value,r.work+4⟩
@[simp] theorem copyBits_value (xs : List Bool) : (copyBits xs).value=xs := by
 induction xs <;> simp_all [copyBits]
@[simp] theorem copyBits_work (xs : List Bool) : (copyBits xs).work=4*xs.length+1 := by
 induction xs <;> simp only [copyBits,List.length_nil,List.length_cons] at * <;> omega

def copiedEqual (xs ys : List Bool) : Charged Bool :=
 let a:=copyBits xs;let b:=copyBits ys;let e:=equalBits a.value b.value
 ⟨e.value,a.work+b.work+e.work+4⟩
@[simp] theorem copiedEqual_value (xs ys : List Bool) : (copiedEqual xs ys).value=(decode xs==decode ys) := by
 simp [copiedEqual]
theorem copiedEqual_work (W : Nat) (xs ys : List Bool) (xl : xs.length≤W) (yl : ys.length≤W) :
 (copiedEqual xs ys).work≤56*(W+1) := by
 have h:=(scalar_width_bounds W xs ys xl yl).1
 simp only [copiedEqual,copyBits_value,copyBits_work];omega
end GenericForest.ScalarBits
