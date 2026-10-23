import RCChooseBound
namespace OrdinaryDispatch.RecoveryControlBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits

/-- Original paths are structural Bool lists, not numeric binary words. -/
def addressEqual : List Bool→List Bool→Charged Bool
 | [],[]=>⟨true,2⟩
 | [],_::_=>⟨false,2⟩
 | _::_,[]=>⟨false,2⟩
 | x::xs,y::ys=>let r:=addressEqual xs ys;⟨(x==y)&&r.value,r.work+4⟩
@[simp] theorem addressEqual_value (xs ys : List Bool) : (addressEqual xs ys).value=(xs==ys) := by
 induction xs generalizing ys with
 | nil=>cases ys <;> rfl
 | cons x xs ih=>cases ys with
  | nil=>rfl
  | cons y ys=>simp [addressEqual,ih]
theorem addressEqual_work (xs ys : List Bool) : (addressEqual xs ys).work≤4*(xs.length+ys.length+1) := by
 induction xs generalizing ys with
 | nil=>cases ys <;> simp only [addressEqual,List.length_nil,List.length_cons] <;> omega
 | cons x xs ih=>cases ys with
  | nil=>simp only [addressEqual,List.length_nil,List.length_cons];omega
  | cons y ys=>have a:=ih ys;simp only [addressEqual,List.length_cons];omega

def ownedAddressEqual (xs ys : List Bool) : Charged Bool :=
 let a:=copyBits xs;let b:=copyBits ys;let e:=addressEqual a.value b.value
 let ca:=closeBits a.value;let cb:=closeBits b.value
 ⟨e.value,a.work+b.work+e.work+ca.work+cb.work+8⟩
@[simp] theorem ownedAddressEqual_value (xs ys : List Bool) : (ownedAddressEqual xs ys).value=(xs==ys) := by simp [ownedAddressEqual]
theorem ownedAddressEqual_work (N : Nat) (xs ys : List Bool) (xn : xs.length≤N) (yn : ys.length≤N) :
 (ownedAddressEqual xs ys).work≤48*(N+1) := by
 have h:=addressEqual_work xs ys
 simp only [ownedAddressEqual,copyBits_work,copyBits_value,closeBits_work];omega

def addressContains (p : List Bool) : List (List Bool)→Charged Bool
 | []=>⟨false,2⟩
 | v::vs=>let e:=ownedAddressEqual p v
   if e.value then ⟨true,e.work+4⟩ else let r:=addressContains p vs;⟨r.value,e.work+r.work+4⟩
@[simp] theorem addressContains_value (p : List Bool) (vs : List (List Bool)) :
 (addressContains p vs).value=vs.contains p := by
 induction vs with
 | nil=>rfl
 | cons v vs ih=>simp [addressContains,ih];split <;> simp_all

theorem addressContains_work (N : Nat) (p : List Bool) (vs : List (List Bool))
 (pn : p.length≤N) (vn : ∀v∈vs,v.length≤N) :
 (addressContains p vs).work≤64*(N+1)*(vs.length+1) := by
 induction vs with
 | nil=>simp only [addressContains,List.length_nil,Nat.zero_add,Nat.mul_one];omega
 | cons v vs ih=>
  have e:=ownedAddressEqual_work N p v pn (vn v (by simp))
  have r:=ih (by intro x hx;exact vn x (by simp [hx]))
  simp only [addressContains,List.length_cons,Nat.mul_add,Nat.mul_one] at r ⊢
  split <;> simp only [Charged.work] <;> omega
end OrdinaryDispatch.RecoveryControlBits
