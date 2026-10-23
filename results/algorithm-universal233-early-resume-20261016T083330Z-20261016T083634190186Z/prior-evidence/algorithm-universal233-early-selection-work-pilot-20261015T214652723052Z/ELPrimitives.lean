import ActualInspection
import EarlyControls
namespace OrdinaryDispatch.EarlyLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence

/-- Unit structural scalar slots: Nat/Bool equality, comparison, increment,
constructor and branch are charged explicitly. No binary provider is asserted. -/
def meterMap {α β : Type} (f : α→Charged β) : List α→Charged (List β)
 | []=>⟨[],1⟩
 | x::xs=>let a:=f x;let r:=meterMap f xs;⟨a.value::r.value,a.work+r.work+4⟩
@[simp] theorem meterMap_value {α β : Type} (f : α→Charged β) (xs : List α) :
 (meterMap f xs).value=xs.map (fun x=>(f x).value) := by induction xs <;> simp_all [meterMap]
theorem meterMap_bound {α β : Type} (f : α→Charged β) (xs : List α) (A : Nat)
 (point : ∀x∈xs,(f x).work≤A) : (meterMap f xs).work≤(A+4)*(xs.length+1) := by
 induction xs with
 | nil=>simp [meterMap]
 | cons x xs ih=>
  have a:=point x (by simp);have b:=ih (fun y hy=>point y (by simp [hy]))
  simp only [meterMap,List.length_cons,Nat.mul_add,Nat.mul_one] at *;omega

def meterFilter {α : Type} (f : α→Charged Bool) : List α→Charged (List α)
 | []=>⟨[],1⟩
 | x::xs=>let a:=f x;let r:=meterFilter f xs;⟨if a.value then x::r.value else r.value,a.work+r.work+4⟩
@[simp] theorem meterFilter_value {α : Type} (f : α→Charged Bool) (xs : List α) :
 (meterFilter f xs).value=xs.filter (fun x=>(f x).value) := by induction xs <;> simp_all [meterFilter,List.filter_cons]
theorem meterFilter_bound {α : Type} (f : α→Charged Bool) (xs : List α) (A : Nat)
 (point : ∀x∈xs,(f x).work≤A) : (meterFilter f xs).work≤(A+4)*(xs.length+1) := by
 induction xs with
 | nil=>simp [meterFilter]
 | cons x xs ih=>
  have a:=point x (by simp);have b:=ih (fun y hy=>point y (by simp [hy]))
  simp only [meterFilter,List.length_cons,Nat.mul_add,Nat.mul_one] at *;omega

def meterFind {α : Type} (f : α→Charged Bool) : List α→Charged (Option α)
 | []=>⟨none,1⟩
 | x::xs=>let a:=f x;if a.value then ⟨some x,a.work+4⟩
   else let r:=meterFind f xs;⟨r.value,a.work+r.work+4⟩
@[simp] theorem meterFind_value {α : Type} (f : α→Charged Bool) (xs : List α) :
 (meterFind f xs).value=xs.find? (fun x=>(f x).value) := by induction xs <;> simp_all [meterFind,List.find?_cons];split <;> simp_all

theorem meterFind_bound {α : Type} (f : α→Charged Bool) (xs : List α) (A : Nat)
 (point : ∀x∈xs,(f x).work≤A) : (meterFind f xs).work≤(A+4)*(xs.length+1) := by
 induction xs with
 | nil=>simp [meterFind]
 | cons x xs ih=>
  have a:=point x (by simp);have b:=ih (fun y hy=>point y (by simp [hy]))
  simp only [meterFind,List.length_cons,Nat.mul_add,Nat.mul_one] at *;split <;> omega

def meterErase (a : Nat) : List Nat→Charged (List Nat)
 | []=>⟨[],1⟩
 | x::xs=>if a==x then ⟨xs,4⟩ else let r:=meterErase a xs;⟨x::r.value,4+r.work⟩
@[simp] theorem meterErase_value (a : Nat) (xs : List Nat) : (meterErase a xs).value=xs.erase a := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>by_cases eq : a=x <;> simp [meterErase,List.erase_cons,ih,eq,Ne.symm eq]
theorem meterErase_bound (a : Nat) (xs : List Nat) : (meterErase a xs).work≤4*(xs.length+1) := by
 induction xs with
 | nil=>simp [meterErase]
 | cons x xs ih=>simp only [meterErase,List.length_cons,Nat.mul_add,Nat.mul_one];split <;> omega

/-- Exact std isPerm traversal, with full suffix overcharge when contains fails. -/
def meterPerm : List Nat→List Nat→Charged Bool
 | [],ys=>⟨ys.isEmpty,1⟩
 | x::xs,ys=>let c:=meterContains x ys;let e:=meterErase x ys;let r:=meterPerm xs e.value
   ⟨c.value&&r.value,c.work+e.work+r.work+4⟩
@[simp] theorem meterPerm_value (xs ys : List Nat) : (meterPerm xs ys).value=decide (xs.Perm ys) := by
 have value : ∀ys,(meterPerm xs ys).value=xs.isPerm ys := by
  induction xs with
  | nil=>intro ys;rfl
  | cons x xs ih=>intro ys;simp [meterPerm,List.isPerm,ih]
 rw [value]
 exact Bool.eq_iff_iff.2 (by simp only [List.isPerm_iff,decide_eq_true_eq])
theorem meterPerm_bound (xs ys : List Nat) :
 (meterPerm xs ys).work≤12*(ys.length+1)*(xs.length+1) := by
 induction xs generalizing ys with
 | nil=>simp [meterPerm];omega
 | cons x xs ih=>
  have a:=meterContains_bound x ys;have b:=meterErase_bound x ys
  have r:=ih ((meterErase x ys).value)
  have le : (meterErase x ys).value.length≤ys.length := by simp only [meterErase_value];exact List.length_erase_le
  have scale:=Nat.mul_le_mul_right (xs.length+1) (Nat.mul_le_mul_left 12 (Nat.add_le_add_right le 1))
  have rr:=Nat.le_trans r scale
  simp only [meterPerm,List.length_cons,Nat.mul_add,Nat.mul_one] at *;omega

/-- DepthOne.proper repeats each leaf materialization for nodup and Perm. -/
def meterOrdinaryProper (T S : Tree) : Charged Bool :=
 let a:=meterLeaves T;let b:=meterNodup a.value
 let c:=meterLeaves S;let d:=meterNodup c.value
 let e:=meterLeaves T;let f:=meterLeaves S;let p:=meterPerm e.value f.value
 ⟨b.value&&d.value&&p.value,a.work+b.work+c.work+d.work+e.work+f.work+p.work+4⟩
@[simp] theorem meterOrdinaryProper_value (T S : Tree) :
 (meterOrdinaryProper T S).value=DepthOne.proper T S := by simp [meterOrdinaryProper,DepthOne.proper]
theorem meterOrdinaryProper_bound (T S : Tree) (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterOrdinaryProper T S).work≤128*(N+1)^2 := by
 have a:=meterLeaves_cap T N tn;have c:=meterLeaves_cap S N sn
 have tl:=Nat.le_trans (leaves_nodes T) tn;have sl:=Nat.le_trans (leaves_nodes S) sn
 have b:=Nat.le_trans (meterNodup_bound (leaves T)) (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right tl 1) 2))
 have d:=Nat.le_trans (meterNodup_bound (leaves S)) (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right sl 1) 2))
 have p:=Nat.le_trans (meterPerm_bound (leaves T) (leaves S))
  (Nat.mul_le_mul (Nat.mul_le_mul_left 12 (Nat.add_le_add_right sl 1)) (Nat.add_le_add_right tl 1))
 have pos : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
 simp only [meterOrdinaryProper,meterLeaves_value]
 simp only [Nat.pow_two,Nat.mul_assoc] at *;omega

end OrdinaryDispatch.EarlyLocalWork
