import BinarySubtract
import Init.Data.Nat.Lemmas
namespace GenericForest.ScalarBits
open Universal233.WholeSourceWork GenericForest.CheckCorrespondence

/-- Mathematical input representation; not a native Nat conversion cost claim. -/
def encode : Nat → Nat → List Bool
 | 0,_=>[]
 | W+1,n=>decide (n%2=1)::encode W (n/2)
@[simp] theorem encode_length (W n : Nat) : (encode W n).length=W := by
 induction W generalizing n <;> simp [encode, *]

theorem bit_mod_two (n : Nat) : bit (decide (n%2=1))=n%2 := by
 have h:=Nat.mod_two_eq_zero_or_one n
 rcases h with h|h <;> simp [h,bit]

theorem encode_value (W n : Nat) (bound : n<2^W) : decode (encode W n)=n := by
 induction W generalizing n with
 | zero=>
  have eq : n=0:=by simpa using bound
  subst n;rfl
 | succ W ih=>
  have quotient : n/2<2^W:=by
   have p:=Nat.mod_add_div n 2
   have m:=Nat.mod_lt n (by decide : 0<2)
   simp only [Nat.pow_succ] at bound
   omega
  simp only [encode,decode,bit_mod_two,ih (n/2) quotient]
  have h:=Nat.mod_add_div n 2;omega

theorem encode_label (n L : Nat) (cap : labelBits n≤L) : decode (encode L n)=n := by
 apply encode_value
 have b:=(Nat.lt_log2_self (n:=n))
 have p:=Nat.pow_le_pow_right (n:=2) (by decide) cap
 exact Nat.lt_of_lt_of_le b p

theorem labelBits_mono (n m : Nat) (h : n≤m) : labelBits n≤labelBits m := by
 by_cases hn : n=0
 · subst n;have hm:=Nat.zero_le m.log2;simp only [labelBits,Nat.log2_zero];omega
 · have hm : m≠0:=by omega
   have bits: n.log2≤m.log2:=(Nat.le_log2 hm).2 (Nat.le_trans (Nat.log2_self_le hn) h)
   unfold labelBits;omega

theorem decode_append (xs ys : List Bool) : decode (xs++ys)=decode xs+2^xs.length*decode ys := by
 induction xs with
 | nil=>simp [decode]
 | cons a as ih=>simp only [List.cons_append,decode,ih,List.length_cons,Nat.pow_succ,Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm (2^as.length) 2];omega

theorem decode_take (xs : List Bool) (W : Nat) (bound : decode xs<2^W) : decode (xs.take W)=decode xs := by
 by_cases len : xs.length≤W
 · rw [List.take_of_length_le len]
 · have eq:=decode_append (xs.take W) (xs.drop W)
   rw [List.take_append_drop] at eq
   have length : (xs.take W).length=W:=by simp only [List.length_take];omega
   rw [length] at eq
   have tailZero : decode (xs.drop W)=0:=by
    by_cases hn : decode (xs.drop W)=0
    · exact hn
    ·
     have pos : 1≤decode (xs.drop W):=by omega
     have h:=Nat.mul_le_mul_left (2^W) pos
     simp only [Nat.mul_one] at h
     omega
   rw [tailZero,Nat.mul_zero,Nat.add_zero] at eq
   exact eq.symm

/-- Fixed-width reference addition. Truncation traversals are explicitly billed. -/
def addAtWidth (W : Nat) (xs ys : List Bool) : Charged (List Bool) :=
 let r:=addBits xs ys
 ⟨r.value.take W,r.work+4*(W+1)⟩

theorem addAtWidth_value (W : Nat) (xs ys : List Bool) (fits : decode xs+decode ys<2^W) :
 decode (addAtWidth W xs ys).value=decode xs+decode ys := by
 simp only [addAtWidth]
 rw [decode_take _ W (by simpa only [addBits_value] using fits),addBits_value]

theorem addAtWidth_work (W : Nat) (xs ys : List Bool) (xl : xs.length≤W) (yl : ys.length≤W) :
 (addAtWidth W xs ys).work≤32*(W+1) := by
 have h:=addCarry_work xs ys false
 simp only [addAtWidth,addBits];omega

theorem scalar_width_bounds (W : Nat) (xs ys : List Bool) (xl : xs.length≤W) (yl : ys.length≤W) :
 (equalBits xs ys).work≤48*(W+1) ∧ (leBits xs ys).work≤48*(W+1) ∧
 (maxBits xs ys).work≤48*(W+1) ∧ (subtractBits xs ys).work≤48*(W+1) := by
 have a:=compare_family_work xs ys
 have b:=subtractBits_work xs ys
 omega

theorem counter_cap_binary (M x : Nat) (bound : x≤4096*(M+1)^8) :
 x<2^(13+8*labelBits (M+1)) := by
 have base : M+1≤2^(labelBits (M+1)):=Nat.le_of_lt (Nat.lt_log2_self (n:=M+1))
 have p:=Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left base 8)
 have form : 4096*(2^labelBits (M+1))^8=2^(12+8*labelBits (M+1)):=by
  rw [←Nat.pow_mul,Nat.mul_comm (labelBits (M+1)) 8,Nat.pow_add]
 rw [form] at p
 have positive : 0<2^(12+8*labelBits (M+1)):=Nat.pow_pos (by decide)
 have grow : 2^(13+8*labelBits (M+1))=2^(12+8*labelBits (M+1))*2:=by
  have e : 13+8*labelBits (M+1)=(12+8*labelBits (M+1))+1:=by omega
  rw [e,Nat.pow_succ]
 rw [grow]
 omega
end GenericForest.ScalarBits
