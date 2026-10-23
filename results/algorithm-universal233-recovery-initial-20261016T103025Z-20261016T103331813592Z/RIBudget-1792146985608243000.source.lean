import RIWords
namespace OrdinaryDispatch.RecoveryInitialBits
open Universal233 WholeSourceWork
open OrdinaryDispatch.RecoveryBits

def zeroBits : Nat→Charged (List Bool)
 | 0=>⟨[],2⟩
 | W+1=>let r:=zeroBits W;⟨false::r.value,r.work+4⟩
@[simp] theorem zeroBits_value (W : Nat) : (zeroBits W).value=List.replicate W false := by induction W <;> simp_all [zeroBits,List.replicate_succ]
@[simp] theorem zeroBits_work (W : Nat) : (zeroBits W).work=4*W+2 := by induction W <;> simp only [zeroBits] at * <;> omega

def takeCopy : Nat→List Bool→Charged (List Bool)
 | 0,_=>⟨[],2⟩
 | _+1,[]=>⟨[],2⟩
 | W+1,b::bs=>let r:=takeCopy W bs;⟨b::r.value,r.work+4⟩
@[simp] theorem takeCopy_value (W : Nat) (xs : List Bool) : (takeCopy W xs).value=xs.take W := by
 induction W generalizing xs with
 | zero=>rfl
 | succ W ih=>cases xs <;> simp_all [takeCopy]
theorem takeCopy_work (W : Nat) (xs : List Bool) : (takeCopy W xs).work≤4*W+2 := by
 induction W generalizing xs with
 | zero=>simp [takeCopy]
 | succ W ih=>cases xs with
  | nil=>simp [takeCopy];omega
  | cons b bs=>have a:=ih bs;simp only [takeCopy];omega

def stepLength (W : Nat) (xs : List Bool) : Charged (List Bool) :=
 let raw:=addCarry true xs [];let c:=takeCopy W raw.value
 let a:=closeBits raw.value;let b:=closeBits xs
 ⟨c.value,raw.work+c.work+a.work+b.work+8⟩
@[simp] theorem stepLength_length (W : Nat) (xs : List Bool) : (stepLength W xs).value.length≤W := by
 simp only [stepLength,takeCopy_value,List.length_take];exact Nat.min_le_left _ _
theorem stepLength_value (W : Nat) (xs : List Bool) (fits : decode xs+1<2^W) :
 decode (stepLength W xs).value=decode xs+1 := by
 have raw:=addCarry_value xs [] true
 simp only [decode,bit,ite_true,Nat.add_zero] at raw
 simp only [stepLength,takeCopy_value]
 rw [decode_take _ W (by simpa only [raw] using fits),raw]
theorem stepLength_work (W : Nat) (xs : List Bool) (xw : xs.length≤W) :
 (stepLength W xs).work≤64*(W+1) := by
 have a:=addCarry_work xs [] true
 have b:=addCarry_length xs [] true
 have c:=takeCopy_work W (addCarry true xs []).value
 simp only [List.length_nil,Nat.max_zero] at a b
 simp only [stepLength,closeBits_work];omega

def lengthOwned {α : Type} (W : Nat) : List α→Charged (List Bool)
 | []=>zeroBits W
 | _::xs=>let r:=lengthOwned W xs;let s:=stepLength W r.value;⟨s.value,r.work+s.work+4⟩
@[simp] theorem lengthOwned_length {α : Type} (W : Nat) (xs : List α) : (lengthOwned W xs).value.length≤W := by
 cases xs <;> simp [lengthOwned]
@[simp] theorem lengthOwned_value {α : Type} (W : Nat) (xs : List α) (fits : xs.length<2^W) :
 decode (lengthOwned W xs).value=xs.length := by
 induction xs with
 | nil=>simp [lengthOwned,decode_replicate_false]
 | cons x xs ih=>
  have tail:xs.length<2^W:=by simp only [List.length_cons] at fits;omega
  simp only [lengthOwned]
  rw [stepLength_value W _ (by simpa only [ih tail,List.length_cons] using fits),ih tail]
  rfl
theorem lengthOwned_work {α : Type} (W : Nat) (xs : List α) :
 (lengthOwned W xs).work≤72*(W+1)*(xs.length+1) := by
 induction xs with
 | nil=>simp only [lengthOwned,zeroBits_work,List.length_nil,Nat.zero_add,Nat.mul_one];omega
 | cons x xs ih=>
  have a:=stepLength_work W (lengthOwned W xs).value (lengthOwned_length W xs)
  simp only [lengthOwned,List.length_cons,Nat.mul_add,Nat.mul_one] at ih ⊢
  omega

def ownedSubtract (xs ys : List Bool) : Charged (List Bool) :=
 let p:=alignBits xs ys;let raw:=subtractBorrow false p.value.1 p.value.2
 let c:=copyBits (if raw.value.1 then [] else raw.value.2)
 let a:=closeBits p.value.1;let b:=closeBits p.value.2;let r:=closeBits raw.value.2
 ⟨c.value,p.work+raw.work+c.work+a.work+b.work+r.work+12⟩
@[simp] theorem ownedSubtract_value (xs ys : List Bool) : decode (ownedSubtract xs ys).value=decode xs-decode ys := by
 simpa only [ownedSubtract,copyBits_value,subtractBits] using subtractBits_value xs ys
@[simp] theorem ownedSubtract_length (xs ys : List Bool) : (ownedSubtract xs ys).value.length≤max xs.length ys.length := by
 simpa only [ownedSubtract,copyBits_value,subtractBits] using subtractBits_length xs ys

theorem ownedSubtract_work (W : Nat) (xs ys : List Bool) (xw : xs.length≤W) (yw : ys.length≤W) :
 (ownedSubtract xs ys).work≤96*(W+1) := by
 have a:=alignBits_work xs ys;have ls:=alignBits_length xs ys
 have b:=subtractBorrow_work (alignBits xs ys).value.1 (alignBits xs ys).value.2 false
 have lr:=subtractBorrow_length (alignBits xs ys).value.1 (alignBits xs ys).value.2 false
 have out:(if (subtractBorrow false (alignBits xs ys).value.1 (alignBits xs ys).value.2).value.1 then [] else
  (subtractBorrow false (alignBits xs ys).value.1 (alignBits xs ys).value.2).value.2).length≤W:=by split <;> simp_all;omega
 simp only [ownedSubtract,copyBits_work,closeBits_work]
 omega

def clipOwned {α : Type} (W : Nat) (budget : List Bool) (xs : List α) : Charged (List Bool) :=
 let n:=lengthOwned W xs;let s:=ownedSubtract n.value [true];let m:=minBits budget s.value
 let a:=closeBits n.value;let b:=closeBits s.value
 ⟨m.value,n.work+s.work+m.work+a.work+b.work+8⟩
@[simp] theorem clipOwned_value {α : Type} (W : Nat) (budget : List Bool) (xs : List α) (fits : xs.length<2^W) :
 decode (clipOwned W budget xs).value=min (decode budget) (xs.length-1) := by
 simp [clipOwned,lengthOwned_value W xs fits,decode,bit]
theorem clipOwned_length {α : Type} (W : Nat) (budget : List Bool) (xs : List α)
 (positive : 1≤W) (bw : budget.length≤W) : (clipOwned W budget xs).value.length≤W := by
 have n:=lengthOwned_length W xs
 have s:=ownedSubtract_length (lengthOwned W xs).value [true]
 have sw:(ownedSubtract (lengthOwned W xs).value [true]).value.length≤W:=by simp only [List.length_cons,List.length_nil] at s;omega
 exact minBits_length W budget _ bw sw

theorem clipOwned_work {α : Type} (W : Nat) (budget : List Bool) (xs : List α)
 (positive : 1≤W) (bw : budget.length≤W) :
 (clipOwned W budget xs).work≤256*(W+1)*(xs.length+1) := by
 have n:=lengthOwned_length W xs
 have s:=ownedSubtract_length (lengthOwned W xs).value [true]
 have sw:(ownedSubtract (lengthOwned W xs).value [true]).value.length≤W:=by simp only [List.length_cons,List.length_nil] at s;omega
 have a:=lengthOwned_work W xs
 have b:=ownedSubtract_work W (lengthOwned W xs).value [true] n (by simpa)
 have c:=minBits_work W budget _ bw sw
 have one:W+1≤(W+1)*(xs.length+1):=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (W+1) (show 1≤xs.length+1 by omega)
 simp only [clipOwned,closeBits_work,Nat.mul_assoc] at a ⊢
 omega
end OrdinaryDispatch.RecoveryInitialBits
