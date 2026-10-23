import PersistentFamilies
namespace GenericForest.BinaryProvider
open Universal233.WholeSourceWork GenericForest.ScalarBits GenericForest.CheckCorrespondence

def bitsCapacity : Bits→Charged Capacity
 | []=>⟨[],1⟩
 | _::xs=>let r:=bitsCapacity xs;⟨()::r.value,r.work+4⟩
@[simp] theorem bitsCapacity_length (xs : Bits) : (bitsCapacity xs).value.length=xs.length := by
 induction xs <;> simp_all [bitsCapacity]
@[simp] theorem bitsCapacity_work (xs : Bits) : (bitsCapacity xs).work=4*xs.length+1 := by
 induction xs <;> simp only [bitsCapacity,List.length_nil,List.length_cons] at * <;> omega

/-- The longer immutable capacity tail can be shared. The traversed prefix is
newly allocated; no native number conversion or length branch occurs. -/
def widenCapacity : Capacity→Bits→Charged Capacity
 | [],xs=>bitsCapacity xs
 | C,[]=>⟨C,1⟩
 | _::C,_::xs=>let r:=widenCapacity C xs;⟨()::r.value,r.work+4⟩
@[simp] theorem widenCapacity_length (C : Capacity) (xs : Bits) :
 (widenCapacity C xs).value.length=max C.length xs.length := by
 induction C generalizing xs with
 | nil=>simp [widenCapacity]
 | cons c C ih=>cases xs <;> simp [widenCapacity,ih]
@[simp] theorem widenCapacity_work (C : Capacity) (xs : Bits) :
 (widenCapacity C xs).work=4*xs.length+1 := by
 induction C generalizing xs with
 | nil=>simp [widenCapacity]
 | cons c C ih=>
  cases xs with
  | nil=>simp [widenCapacity]
  | cons b bs=>have h:=ih bs;simp only [widenCapacity,List.length_cons] at h ⊢;omega

def labelsCapacity : Block→Charged Capacity
 | []=>⟨[()],5⟩
 | x::xs=>let r:=labelsCapacity xs;let c:=widenCapacity r.value x;⟨c.value,r.work+c.work+4⟩
theorem labelsCapacity_positive (L : Block) : 0<(labelsCapacity L).value.length := by
 induction L with
 | nil=>simp [labelsCapacity]
 | cons x xs ih=>simp only [labelsCapacity,widenCapacity_length];omega
theorem labelsCapacity_width (L : Block) : BlockWidth (labelsCapacity L).value.length L := by
 induction L with
 | nil=>intro x hx;simp at hx
 | cons x xs ih=>
  intro y hy
  simp only [labelsCapacity,widenCapacity_length,LabelWidth]
  rcases List.mem_cons.mp hy with rfl|hy
  · exact Nat.le_max_right _ _
  · exact Nat.le_trans (ih y hy) (Nat.le_max_left _ _)

/-- An unbounded bit counter measures the actual list spine. The result remains
bits, and its bit spine supplies finite counter capacity for subsequent runs. -/
def spineCounter {α : Type} : List α→Charged Bits
 | []=>⟨[],1⟩
 | _::xs=>let r:=spineCounter xs;let a:=incrementBits r.value;⟨a.value,r.work+a.work+4⟩
@[simp] theorem spineCounter_value {α : Type} (xs : List α) : decode (spineCounter xs).value=xs.length := by
 induction xs <;> simp_all [spineCounter,decode]
theorem spineCounter_length {α : Type} (xs : List α) : (spineCounter xs).value.length≤xs.length := by
 induction xs with
 | nil=>simp [spineCounter]
 | cons x xs ih=>
  have a:=addCarry_length (spineCounter xs).value [] true
  simp only [spineCounter,incrementBits,List.length_cons,List.length_nil,Nat.max_zero] at a ⊢;omega
theorem spineCounter_work {α : Type} (xs : List α) : (spineCounter xs).work≤16*(xs.length+1)^2 := by
 induction xs with
 | nil=>simp [spineCounter]
 | cons x xs ih=>
  have a:=addCarry_work (spineCounter xs).value [] true
  have l:=spineCounter_length xs
  simp only [spineCounter,incrementBits,List.length_cons,List.length_nil,Nat.add_zero,Nat.pow_two,
   Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul] at a ih ⊢;omega

/-- Setup is an executed, paid traversal of the supplied domain and actual
forest payload. The later checker pays its own repeated materializations. -/
def prepareCapacity (L : Block) (F : Forest) : Charged Capacity :=
 let cells:=flattenLabels F;let domain:=appendLabels L cells.value
 let labels:=labelsCapacity domain.value;let count:=spineCounter cells.value
 let cap:=widenCapacity labels.value count.value
 ⟨cap.value,cells.work+domain.work+labels.work+count.work+cap.work+8⟩

theorem prepareCapacity_spec (L : Block) (F : Forest) :
 let C:=(prepareCapacity L F).value
 BlockWidth C.length L ∧ ForestWidth C.length F ∧ 0<C.length ∧ F.flatten.length<2^C.length := by
 let A:=L++F.flatten
 let K:=(labelsCapacity A).value.length
 let J:=(spineCounter F.flatten).value.length
 have len : (prepareCapacity L F).value.length=max K J:=by
  simp only [prepareCapacity,flattenLabels_value,appendLabels_value,widenCapacity_length];rfl
 have aw:=labelsCapacity_width A
 have pos:=labelsCapacity_positive A
 have cap : BlockWidth (max K J) A:=fun x hx=>Nat.le_trans (aw x hx) (Nat.le_max_left _ _)
 have fits:=decode_bound (spineCounter F.flatten).value
 rw [spineCounter_value] at fits
 have power:=Nat.pow_le_pow_right (n:=2) (by decide) (Nat.le_max_right K J)
 dsimp only
 rw [len]
 refine ⟨?_,?_,by omega,Nat.lt_of_lt_of_le fits power⟩
 · intro x hx;exact cap x (List.mem_append_left _ hx)
 · intro B hB x hx
   exact cap x (List.mem_append_right _ (List.mem_flatten.mpr ⟨B,hB,hx⟩))

/-- Complete standalone partition entry point, including measured setup. -/
def partitionFromInput (L : Block) (F : Forest) : Charged Bool :=
 let c:=prepareCapacity L F;let p:=partitionLabels c.value L F
 ⟨p.value,c.work+p.work+4⟩

theorem partitionFromInput_value (L : Block) (F : Forest) :
 (partitionFromInput L F).value=RMAF.partitionCheck (blockValue L) (forestValue F) := by
 have s:=prepareCapacity_spec L F
 have p:=partitionLabels_projects (prepareCapacity L F).value.length (prepareCapacity L F).value L F
  (Nat.le_refl _) s.2.2.1 s.1 s.2.1 s.2.2.2
 exact p.1.trans (meterPartition_value _ _)

theorem partitionFromInput_work (L : Block) (F : Forest) :
 (partitionFromInput L F).work≤(prepareCapacity L F).work+
  ScalarBits.beta (prepareCapacity L F).value.length*(meterPartition (blockValue L) (forestValue F)).work+4 := by
 have s:=prepareCapacity_spec L F
 have p:=partitionLabels_projects (prepareCapacity L F).value.length (prepareCapacity L F).value L F
  (Nat.le_refl _) s.2.2.1 s.1 s.2.1 s.2.2.2
 have cost:=p.2
 dsimp only [partitionFromInput];omega

theorem labelsCapacity_length_bound (L : Block) : (labelsCapacity L).value.length≤L.flatten.length+1 := by
 induction L with
 | nil=>simp [labelsCapacity]
 | cons x xs ih=>
  simp only [labelsCapacity,widenCapacity_length,List.flatten_cons,List.length_append];omega

/-- Width is determined by the supplied finite domain and actual state, never
by a desired solver-work field. This conservative bound does not assert a
logarithmic whole-program scalar bound. -/
theorem prepareCapacity_width_bound (L : Block) (F : Forest) :
 (prepareCapacity L F).value.length≤L.flatten.length+F.flatten.flatten.length+F.flatten.length+1 := by
 have a:=labelsCapacity_length_bound (L++F.flatten)
 have b:=spineCounter_length F.flatten
 simp only [List.flatten_append,List.length_append] at a
 simp only [prepareCapacity,flattenLabels_value,appendLabels_value,widenCapacity_length];omega

@[simp] theorem appendLabels_work_exact (A B : Block) :
 (appendLabels A B).work=4*A.flatten.length+5*A.length+1 := by
 induction A with
 | nil=>simp [appendLabels]
 | cons x xs ih=>
  simp only [appendLabels,copyBits_work,List.flatten_cons,List.length_append,List.length_cons] at ih ⊢;omega
@[simp] theorem flattenLabels_work_exact (F : Forest) :
 (flattenLabels F).work=4*F.flatten.flatten.length+5*F.flatten.length+5*F.length+1 := by
 induction F with
 | nil=>simp [flattenLabels]
 | cons B F ih=>
  simp only [flattenLabels,appendLabels_work_exact,List.flatten_cons,List.flatten_append,List.length_append,List.length_cons] at ih ⊢;omega
@[simp] theorem labelsCapacity_work_exact (L : Block) :
 (labelsCapacity L).work=4*L.flatten.length+5*L.length+5 := by
 induction L with
 | nil=>simp [labelsCapacity]
 | cons x xs ih=>
  simp only [labelsCapacity,widenCapacity_work,List.flatten_cons,List.length_append,List.length_cons] at ih ⊢;omega

theorem prepareCapacity_work_bound (L : Block) (F : Forest) :
 (prepareCapacity L F).work≤8*(L.flatten.length+F.flatten.flatten.length)+
  10*L.length+14*F.flatten.length+5*F.length+16*(F.flatten.length+1)^2+16 := by
 have n:=spineCounter_work F.flatten
 have l:=spineCounter_length F.flatten
 simp only [prepareCapacity,flattenLabels_value,appendLabels_value,flattenLabels_work_exact,
  appendLabels_work_exact,labelsCapacity_work_exact,widenCapacity_work,List.flatten_append,List.length_append]
 omega
end GenericForest.BinaryProvider
