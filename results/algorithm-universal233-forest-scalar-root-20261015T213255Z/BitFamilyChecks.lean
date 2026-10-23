import BitHullChecks
namespace GenericForest.ScalarBits
open RMAF RestrictionBridge Universal233 Universal233.WholeSourceWork GenericForest.CheckCorrespondence

def bitNodup (W : Nat) : List Nat→Charged Bool
 | []=>⟨true,beta W⟩
 | x::xs=>let c:=bitContains W x xs;let r:=bitNodup W xs;⟨!c.value&&r.value,c.work+r.work+4*beta W⟩
theorem bitNodup_refines (W : Nat) (L : List Nat) (cap : LabelCap W L) :
 Refines W (bitNodup W L) (meterNodup L) := by
 induction L with
 | nil=>simp [Refines,bitNodup,meterNodup]
 | cons x xs ih=>
  have tail : LabelCap W xs:=fun y hy=>cap y (by simp [hy])
  have c:=bitContains_refines W x xs (cap x (by simp)) tail
  have r:=ih tail
  simp only [Refines] at c r ⊢
  simp only [bitNodup,meterNodup,c.1,r.1]
  refine ⟨by trivial,?_⟩
  simp only [Nat.mul_add,Nat.mul_comm (beta W) 4];omega

def bitContained (W : Nat) (B U : List Nat) :=bitAll W (fun x=>bitContains W x U) B
theorem bitContained_refines (W : Nat) (B U : List Nat) (bc : LabelCap W B) (uc : LabelCap W U) :
 Refines W (bitContained W B U) (meterContained B U) :=
 bitAll_refines W _ _ B (fun x hx=>bitContains_refines W x U (bc x hx) uc)

def bitFamily (W : Nat) (U : List Nat) : Forest→Charged Forest
 | []=>⟨[],beta W⟩
 | B::F=>let c:=bitContained W B U;let r:=bitFamily W U F
          ⟨if c.value then B::r.value else r.value,c.work+r.work+6*beta W⟩
theorem bitFamily_refines (W : Nat) (U : List Nat) (F : Forest) (uc : LabelCap W U)
 (blocks : ∀B∈F,LabelCap W B) : Refines W (bitFamily W U F) (meterFamily U F) := by
 induction F with
 | nil=>simp [Refines,bitFamily,meterFamily]
 | cons B F ih=>
  have c:=bitContained_refines W B U (blocks B (by simp)) uc
  have r:=ih (fun C hc=>blocks C (by simp [hc]))
  simp only [Refines] at c r ⊢
  simp only [bitFamily,meterFamily,c.1,r.1]
  refine ⟨by trivial,?_⟩
  simp only [Nat.mul_add,Nat.mul_comm (beta W) 6];omega

theorem block_cap (W : Nat) (F : Forest) (cap : LabelCap W F.flatten) (B : List Nat) (h : B∈F) : LabelCap W B :=
 fun x hx=>cap x (List.mem_flatten.mpr ⟨B,h,hx⟩)
theorem family_cap (W : Nat) (U : List Nat) (F : Forest) (cap : LabelCap W F.flatten) :
 LabelCap W (family U F).flatten := by
 intro x hx
 obtain ⟨B,hB,hx⟩:=List.mem_flatten.mp hx
 exact block_cap W F cap B (List.mem_filter.mp hB).1 x hx
end GenericForest.ScalarBits
