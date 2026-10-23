import FreshEnvelope
namespace Universal233.Rule5LocalWork
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller
structure Measured (α : Type) where
 value : α
 work : Nat
 deriving Repr

/-- Scan/constructor units. A Nat comparison is charged at its caller-supplied
scalar cost, never asserted to have unit bit cost. This companion conservatively
pays the whole membership list even when contains stops earlier. -/
def filterMeter (X : List Nat) : List Nat→Measured (List Nat)
 | [] => ⟨[],1⟩
 | x::xs => let r:=filterMeter X xs
            ⟨if X.contains x then x::r.value else r.value,X.length+2+r.work⟩

theorem filter_value (X xs : List Nat) : (filterMeter X xs).value=xs.filter (X.contains ·) := by
 induction xs with
 | nil => rfl
 | cons x xs ih => simp only [filterMeter,List.filter_cons];split <;> simp_all

theorem filter_work (X xs : List Nat) : (filterMeter X xs).work=(X.length+2)*xs.length+1 := by
 induction xs with
 | nil => simp [filterMeter]
 | cons x xs ih => simp only [filterMeter,List.length_cons,ih];rw [Nat.mul_add,Nat.mul_one];omega

/-- List equality is a named primitive: at most H.length+B.length+1 cell/
scalar visits. Includes unsuccessful comparisons before the first equal owner. -/
def eraseMeter (H : List Nat) : Forest→Measured Forest
 | [] => ⟨[],1⟩
 | B::F => if H==B then ⟨F,H.length+B.length+2⟩
           else let r:=eraseMeter H F
                ⟨B::r.value,H.length+B.length+2+r.work⟩

theorem erase_value (H : List Nat) (F : Forest) : (eraseMeter H F).value=F.erase H := by
 induction F with
 | nil => rfl
 | cons B F ih =>
   simp only [eraseMeter,List.erase_cons]
   have eq : (H==B)=(B==H) := by apply Bool.eq_iff_iff.2;simp only [beq_iff_eq];exact eq_comm
   rw [eq]
   split <;> simp_all

theorem erase_work (H : List Nat) (F : Forest) :
 (eraseMeter H F).work≤(H.length+2)*F.length+F.flatten.length+1 := by
 induction F with
 | nil => simp [eraseMeter]
 | cons B F ih =>
   simp only [eraseMeter]
   split <;> simp only [List.length_cons,List.flatten_cons,List.length_append,
     Nat.mul_add,Nat.mul_one] <;> omega

/-- One LITERAL owner pair: two membership filters, two first-owner erases,
then the original merged constructor and append. No owner-success oracle. -/
def pairMeter (X Y : List Nat) (GM GN : Forest) (H J : List Nat) : Measured Forest :=
 let K:=filterMeter X H;let L:=filterMeter Y J
 let FX:=eraseMeter H GM;let FY:=eraseMeter J GN
 ⟨merged K.value L.value FX.value FY.value,
 K.work+L.work+FX.work+FY.work+K.value.length+FX.value.length+1⟩

theorem pair_value (X Y : List Nat) (GM GN : Forest) (H J : List Nat) :
 (pairMeter X Y GM GN H J).value=
 merged (H.filter (X.contains ·)) (J.filter (Y.contains ·)) (GM.erase H) (GN.erase J) := by
 simp [pairMeter,filter_value,erase_value]

theorem block_len (F : Forest) (H : List Nat) (mem : H∈F) : H.length≤F.flatten.length :=
 (List.sublist_flatten_of_mem mem).length_le

theorem pair_work (X Y : List Nat) (GM GN : Forest) (H J : List Nat) (N : Nat)
 (hX : X.length≤N) (hY : Y.length≤N) (hM : cells GM≤N) (hN : cells GN≤N)
 (hH : H.length≤N) (hJ : J.length≤N) :
 (pairMeter X Y GM GN H J).work≤8*(N+2)^2 := by
 have hm : GM.length≤N ∧ GM.flatten.length≤N := by unfold cells at hM;omega
 have hn : GN.length≤N ∧ GN.flatten.length≤N := by unfold cells at hN;omega
 have k := List.length_filter_le (X.contains ·) H
 have fx : (GM.erase H).length≤GM.length := List.length_erase_le
 have ek := erase_work H GM
 have el := erase_work J GN
 have fk := filter_work X H
 have fl := filter_work Y J
 have p1 := Nat.mul_le_mul (Nat.add_le_add_right hX 2) hH
 have p2 := Nat.mul_le_mul (Nat.add_le_add_right hY 2) hJ
 have p3 := Nat.mul_le_mul (Nat.add_le_add_right hH 2) hm.1
 have p4 := Nat.mul_le_mul (Nat.add_le_add_right hJ 2) hn.1
 rw [←filter_value] at k
 rw [←erase_value] at fx
 simp only [pairMeter]
 simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one,Nat.mul_add,Nat.add_mul,Nat.one_mul] at *
 omega
end Universal233.Rule5LocalWork
