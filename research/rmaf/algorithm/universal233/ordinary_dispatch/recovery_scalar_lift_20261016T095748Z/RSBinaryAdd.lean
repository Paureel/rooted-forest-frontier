import RSBinaryCompare
namespace OrdinaryDispatch.RecoveryBits
open Universal233.WholeSourceWork

def sumBit (a b c : Bool) := (a.xor b).xor c
def carryBit (a b c : Bool) := (a&&b)||(a&&c)||(b&&c)
theorem digit_add (a b c : Bool) : bit (sumBit a b c)+2*bit (carryBit a b c)=bit a+bit b+bit c := by
 cases a <;> cases b <;> cases c <;> decide

def addCarry (c : Bool) : List Bool → List Bool → Charged (List Bool)
 | [],[]=>⟨if c then [true] else [],4⟩
 | a::as,[]=>let r:=addCarry (carryBit a false c) as [];⟨sumBit a false c::r.value,r.work+12⟩
 | [],b::bs=>let r:=addCarry (carryBit false b c) [] bs;⟨sumBit false b c::r.value,r.work+12⟩
 | a::as,b::bs=>let r:=addCarry (carryBit a b c) as bs;⟨sumBit a b c::r.value,r.work+12⟩
termination_by xs ys=>xs.length+ys.length

theorem addCarry_value (xs ys : List Bool) (c : Bool) :
 decode (addCarry c xs ys).value=decode xs+decode ys+bit c := by
 induction xs generalizing ys c with
 | nil=>
  induction ys generalizing c with
  | nil=>cases c <;> simp [addCarry,decode,bit]
  | cons b bs ih=>
   have h:=ih (carryBit false b c)
   have d:=digit_add false b c
   simp only [addCarry,decode,bit,Bool.false_eq_true,ite_false] at h d ⊢
   omega
 | cons a as ih=>
  cases ys with
  | nil=>
   have h:=ih [] (carryBit a false c)
   have d:=digit_add a false c
   simp only [addCarry,decode,bit,Bool.false_eq_true,ite_false] at h d ⊢
   omega
  | cons b bs=>
   have h:=ih bs (carryBit a b c)
   have d:=digit_add a b c
   simp only [addCarry,decode] at h d ⊢
   omega

theorem addCarry_work (xs ys : List Bool) (c : Bool) :
 (addCarry c xs ys).work≤12*(xs.length+ys.length+1) := by
 induction xs generalizing ys c with
 | nil=>
  induction ys generalizing c with
  | nil=>simp [addCarry]
  | cons b bs ih=>have h:=ih (carryBit false b c);simp only [addCarry,List.length_nil,List.length_cons] at *;omega
 | cons a as ih=>
  cases ys with
  | nil=>have h:=ih [] (carryBit a false c);simp only [addCarry,List.length_nil,List.length_cons] at *;omega
  | cons b bs=>have h:=ih bs (carryBit a b c);simp only [addCarry,List.length_cons] at *;omega

theorem addCarry_length (xs ys : List Bool) (c : Bool) :
 (addCarry c xs ys).value.length≤max xs.length ys.length+1 := by
 induction xs generalizing ys c with
 | nil=>
  induction ys generalizing c with
  | nil=>cases c <;> simp [addCarry]
  | cons b bs ih=>have h:=ih (carryBit false b c);simp only [addCarry,List.length_nil,List.length_cons,Nat.zero_max] at *;omega
 | cons a as ih=>
  cases ys with
  | nil=>have h:=ih [] (carryBit a false c);simp only [addCarry,List.length_nil,List.length_cons,Nat.max_zero] at *;omega
  | cons b bs=>have h:=ih bs (carryBit a b c);simp only [addCarry,List.length_cons] at *;omega

def addBits (xs ys : List Bool) := addCarry false xs ys
@[simp] theorem addBits_value (xs ys : List Bool) : decode (addBits xs ys).value=decode xs+decode ys := by
 simpa only [addBits,bit,Bool.false_eq_true,ite_false,Nat.add_zero] using addCarry_value xs ys false

def incrementBits (xs : List Bool) := addCarry true xs []
@[simp] theorem incrementBits_value (xs : List Bool) : decode (incrementBits xs).value=decode xs+1 := by
 simpa [incrementBits,bit,decode] using addCarry_value xs [] true
end OrdinaryDispatch.RecoveryBits
