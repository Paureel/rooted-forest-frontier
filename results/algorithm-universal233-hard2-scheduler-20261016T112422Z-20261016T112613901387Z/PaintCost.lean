import Hard2SourceBill
namespace AllGoodDP.LocalWork
open RMAF Universal233.WholeSourceWork

def paintNodes : Paint → Nat
 | .leaf _ _ => 1
 | .node _ l r => 1+paintNodes l+paintNodes r

theorem paintNodes_pos (p : Paint) : 1≤paintNodes p := by cases p <;> simp only [paintNodes] <;> omega
@[simp] theorem paintNodes_erase (p : Paint) : paintNodes p=Universal233.CoreWork.treeNodes (erase p) := by
 induction p with
 | leaf => rfl
 | node c l r il ir => simp [paintNodes,erase,Universal233.CoreWork.treeNodes,il,ir]

def meterChanges : Paint → Charged Nat
 | .leaf _ _ => ⟨0,4⟩
 | .node c l r =>
  let a := meterChanges l
  let b := meterChanges r
  ⟨a.value+delta c (root l)+b.value+delta c (root r),a.work+b.work+16⟩
@[simp] theorem meterChanges_value (p : Paint) : (meterChanges p).value=changes p := by
 induction p with
 | leaf => rfl
 | node c l r il ir => simp [meterChanges,changes,il,ir]
theorem meterChanges_work (p : Paint) : (meterChanges p).work≤16*paintNodes p := by
 induction p with
 | leaf => simp [meterChanges,paintNodes]
 | node c l r il ir => simp only [meterChanges,paintNodes,Nat.mul_add,Nat.mul_one];omega

def meterEdgeCost (c : Nat) (p : Paint) : Charged Nat :=
 let m := meterChanges p
 ⟨m.value+delta c (root p),m.work+8⟩
@[simp] theorem meterEdgeCost_value (c : Nat) (p : Paint) : (meterEdgeCost c p).value=edgeCost c p := by simp [meterEdgeCost,edgeCost]
theorem meterEdgeCost_work (c : Nat) (p : Paint) : (meterEdgeCost c p).work≤24*paintNodes p := by
 have h := meterChanges_work p
 have pos := paintNodes_pos p
 simp only [meterEdgeCost]
 omega

/-- Literal tail-first best. Both actual candidate costs are recomputed in each
comparison, with their full paint scan work retained. -/
def meterBest {α : Type} (cost : α → Charged Nat) : List α → Charged (Option α)
 | [] => ⟨none,4⟩
 | a::as =>
  let r := meterBest cost as
  match r.value with
  | none => ⟨some a,r.work+8⟩
  | some b =>
   let ca := cost a
   let cb := cost b
   ⟨if ca.value≤cb.value then some a else some b,r.work+ca.work+cb.work+12⟩
@[simp] theorem meterBest_value {α : Type} (cost : α → Charged Nat) (xs : List α) :
 (meterBest cost xs).value=RMAF.best (fun a=>(cost a).value) (fun _=>true) xs := by
 induction xs with
 | nil => rfl
 | cons a as ih => simp only [meterBest,ih,RMAF.best];cases h:RMAF.best (fun a=>(cost a).value) (fun _=>true) as <;> simp

theorem meterBest_work {α : Type} (cost : α → Charged Nat) (xs : List α) (C : Nat)
 (cap : ∀a,a∈xs→(cost a).work≤C) :
 (meterBest cost xs).work≤(2*C+12)*xs.length+4 := by
 induction xs with
 | nil => simp [meterBest]
 | cons a as ih =>
  have tail := ih (fun a ha=>cap a (by simp [ha]))
  have head := cap a (by simp)
  cases h:(meterBest cost as).value with
  | none => simp only [meterBest,h,List.length_cons,Nat.mul_add,Nat.mul_one];omega
  | some b =>
   have hb : b∈as := (RMAF.best_spec (fun a=>(cost a).value) (fun _=>true) as b ((meterBest_value cost as).symm.trans h)).1
   have bound := cap b (by simp [hb])
   simp only [meterBest,h,List.length_cons,Nat.mul_add,Nat.mul_one]
   omega

def meterChoose (cost : Paint → Charged Nat) (xs : List Paint) : Charged Paint :=
 let m := meterBest cost xs
 ⟨m.value.getD (.leaf 0 0),m.work+4⟩
@[simp] theorem meterChoose_value (cost : Paint → Charged Nat) (xs : List Paint) :
 (meterChoose cost xs).value=choose (fun a=>(cost a).value) xs := by simp [meterChoose,choose]
theorem meterChoose_work (cost : Paint → Charged Nat) (xs : List Paint) (C : Nat)
 (cap : ∀a,a∈xs→(cost a).work≤C) :
 (meterChoose cost xs).work≤(2*C+12)*xs.length+8 := by
 have h := meterBest_work cost xs C cap
 simp only [meterChoose]
 omega
end AllGoodDP.LocalWork
