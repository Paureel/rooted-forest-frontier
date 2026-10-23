import PersistentChecks
namespace GenericForest.BinaryProvider
open Universal233.WholeSourceWork GenericForest.ScalarBits GenericForest.CheckCorrespondence

def lengthRegister {α : Type} (C : Capacity) : List α→Charged Bits
 | []=>zeroRegister C
 | _::xs=>let r:=lengthRegister C xs;let a:=addRegister C r.value [true];⟨a.value,r.work+a.work+4⟩
theorem lengthRegister_length {α : Type} (C : Capacity) (xs : List α) : (lengthRegister C xs).value.length≤C.length := by
 cases xs with
 | nil=>simp [lengthRegister]
 | cons x xs=>exact addRegister_length C _ _
theorem lengthRegister_value {α : Type} (C : Capacity) (xs : List α) (fits : xs.length<2^C.length) :
 decode (lengthRegister C xs).value=xs.length := by
 induction xs with
 | nil=>simp [lengthRegister,decode_replicate_false]
 | cons x xs ih=>
  have tf : xs.length<2^C.length:=by simp only [List.length_cons] at fits;omega
  simp only [lengthRegister]
  rw [addRegister_value C _ [true] (by simpa [ih tf,decode,bit] using fits)]
  simp [ih tf,decode,bit]
theorem lengthRegister_work {α : Type} (C : Capacity) (xs : List α) (cp : 0<C.length) :
 (lengthRegister C xs).work≤40*(C.length+1)*(xs.length+1) := by
 induction xs with
 | nil=>simp only [lengthRegister,zeroRegister_work,List.length_nil,Nat.zero_add,Nat.mul_one];omega
 | cons x xs ih=>
  have a:=addRegister_work C (lengthRegister C xs).value [true] (lengthRegister_length C xs) (by simp;omega)
  simp only [lengthRegister,List.length_cons,Nat.mul_add,Nat.mul_one] at ih ⊢;omega

def acceptedLabels (C : Capacity) (T : Option Tree) (ss : List Tree) (q : Bits) (F : Forest) : Charged Bool:=
 let a:=agreesLabels C T ss F;let fl:=lengthRegister C F;let sl:=lengthRegister C ss
 let d:=subtractBits fl.value sl.value;let e:=leBits d.value q
 ⟨a.value&&e.value,a.work+fl.work+sl.work+d.work+e.work+8⟩
theorem acceptedLabels_projects (W : Nat) (C : Capacity) (T : Option Tree) (ss : List Tree) (q : Bits) (F : Forest)
 (cw : C.length≤W) (cp : 0<C.length) (tc : TargetWidth W T) (sc : SourcesWidth W ss) (qw : q.length≤W)
 (fc : ForestWidth W F) (fitF : F.flatten.length<2^C.length)
 (fitS : (sourceLeavesCopy ss).value.flatten.length<2^C.length)
 (fitFL : F.length<2^C.length) (fitSL : ss.length<2^C.length) :
 Projects W id (acceptedLabels C T ss q F)
  (meterAccepted (targetValue T) (sourcesValue ss) (labelValue q) (forestValue F)) := by
 have a:=agreesLabels_projects W C T ss F cw cp tc sc fc fitF fitS
 have fl:=lengthRegister_value C F fitFL;have sl:=lengthRegister_value C ss fitSL
 have flw:=lengthRegister_length C F;have slw:=lengthRegister_length C ss
 have dw:=subtractBits_length (lengthRegister C F).value (lengthRegister C ss).value
 have dl : (subtractBits (lengthRegister C F).value (lengthRegister C ss).value).value.length≤W:=by omega
 have sub:=subtractBits_work (lengthRegister C F).value (lengthRegister C ss).value
 have e:=(compare_family_work (subtractBits (lengthRegister C F).value (lengthRegister C ss).value).value q).2.1
 have evalue:=leBits_value (subtractBits (lengthRegister C F).value (lengthRegister C ss).value).value q
 have fcost:=Nat.le_trans (lengthRegister_work C F cp)
  (Nat.mul_le_mul_right (F.length+1) (Nat.mul_le_mul_left 40 (Nat.add_le_add_right cw 1)))
 have scost:=Nat.le_trans (lengthRegister_work C ss cp)
  (Nat.mul_le_mul_right (ss.length+1) (Nat.mul_le_mul_left 40 (Nat.add_le_add_right cw 1)))
 simp only [Projects,id_eq] at a ⊢
 simp only [acceptedLabels,meterAccepted]
 constructor
 · simp only [evalue,subtractBits_value,fl,sl,a.1,labelValue,ForestState.additionalCost,forestValue_length,sourcesValue,List.length_map]
 · have cost:=a.2
   simp only [forestValue_length,sourcesValue,List.length_map,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_one] at fcost scost cost ⊢
   unfold ScalarBits.beta at cost ⊢
   simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_one,Nat.mul_left_comm W 6] at cost ⊢;omega

def forestOptionValue (F : Option Forest):=F.map forestValue

def checkedLabels (C : Capacity) (T : Option Tree) (ss : List Tree) (q : Bits) (F : Forest) : Charged (Option Forest):=
 let a:=acceptedLabels C T ss q F
 ⟨if a.value then some F else none,a.work+2⟩
theorem checkedLabels_projects (W : Nat) (C : Capacity) (T : Option Tree) (ss : List Tree) (q : Bits) (F : Forest)
 (cw : C.length≤W) (cp : 0<C.length) (tc : TargetWidth W T) (sc : SourcesWidth W ss) (qw : q.length≤W)
 (fc : ForestWidth W F) (fitF : F.flatten.length<2^C.length)
 (fitS : (sourceLeavesCopy ss).value.flatten.length<2^C.length)
 (fitFL : F.length<2^C.length) (fitSL : ss.length<2^C.length) :
 Projects W forestOptionValue (checkedLabels C T ss q F)
  (meterChecked (targetValue T) (sourcesValue ss) (labelValue q) (forestValue F)) := by
 have a:=acceptedLabels_projects W C T ss q F cw cp tc sc qw fc fitF fitS fitFL fitSL
 have p:=beta_positive W
 simp only [Projects,id_eq] at a ⊢
 simp only [checkedLabels,meterChecked,a.1]
 constructor
 · cases h : (meterAccepted (targetValue T) (sourcesValue ss) (labelValue q) (forestValue F)).value <;> simp [h,forestOptionValue]
 · have c:=a.2;simp only [Nat.mul_add];omega
end GenericForest.BinaryProvider
