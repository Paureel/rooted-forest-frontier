import PaidDomains
set_option linter.unusedSimpArgs false
namespace Universal233.PaidLiteralDecisionWork
open RMAF CoreGraph HardParent CoreWork Rule5PrefixLocalWork Rule5PendantLocalWork Rule5RemainingLocalWork

/-- Source primitive model: scalar Nat/Bool comparison is one inspection.
Recursive constructors and list scans are charged explicitly. No runtime oracle. -/
def treeEqMeter : Tree → Tree → Measured Bool
 | .leaf x,.leaf y=>⟨decide (x=y),2⟩
 | .node a b,.node c d=>
   let l:=treeEqMeter a c
   if l.value then let r:=treeEqMeter b d;⟨r.value,l.work+r.work+2⟩
   else ⟨false,l.work+2⟩
 | _,_=>⟨false,1⟩

theorem tree_eq_value (A B : Tree) : (treeEqMeter A B).value=decide (A=B) := by
 induction A generalizing B with
 | leaf x=>cases B <;> simp [treeEqMeter]
 | node a b ha hb=>
  cases B with
  | leaf y=>simp [treeEqMeter]
  | node c d=>
   simp only [treeEqMeter,ha,hb]
   split <;> simp_all

theorem tree_eq_work (A B : Tree) : (treeEqMeter A B).work≤3*treeNodes A := by
 induction A generalizing B with
 | leaf x=>cases B <;> simp [treeEqMeter,treeNodes]
 | node a b ha hb=>
  cases B with
  | leaf y=>simp [treeEqMeter,treeNodes];omega
  | node c d=>
   have l:=ha c;have r:=hb d
   simp only [treeEqMeter,treeNodes,Nat.mul_add]
   split <;> dsimp only <;> omega

def listEqMeter {α : Type} (f : α→α→Measured Bool) : List α→List α→Measured Bool
 | [],[]=>⟨true,1⟩
 | [],_::_=>⟨false,1⟩
 | _::_,[]=>⟨false,1⟩
 | x::xs,y::ys=>let h:=f x y
                 if h.value then let r:=listEqMeter f xs ys;⟨r.value,h.work+r.work+2⟩
                 else ⟨false,h.work+2⟩

theorem list_eq_value {α : Type} [DecidableEq α] (f : α→α→Measured Bool)
 (v : ∀x y,(f x y).value=decide (x=y)) (xs ys : List α) :
 (listEqMeter f xs ys).value=decide (xs=ys) := by
 induction xs generalizing ys with
 | nil=>cases ys <;> simp [listEqMeter]
 | cons x xs ih=>cases ys with
   | nil=>simp [listEqMeter]
   | cons y ys=>simp only [listEqMeter,v,ih];split <;> simp_all

theorem list_eq_work {α : Type} (f : α→α→Measured Bool) (xs ys : List α) (K : Nat)
 (h : ∀x,x∈xs→∀y,y∈ys→(f x y).work≤K) :
 (listEqMeter f xs ys).work≤(K+2)*xs.length+1 := by
 induction xs generalizing ys with
 | nil=>cases ys <;> simp [listEqMeter]
 | cons x xs ih=>cases ys with
   | nil=>simp [listEqMeter]
   | cons y ys=>
    have head:=h x (by simp) y (by simp)
    have tail:=ih ys (by intro z hz w hw;exact h z (by simp [hz]) w (by simp [hw]))
    simp only [listEqMeter,List.length_cons,Nat.mul_succ]
    split <;> dsimp only <;> omega

def natEqMeter (x y : Nat) : Measured Bool := ⟨decide (x=y),1⟩
def natListEqMeter := listEqMeter natEqMeter

theorem nat_list_eq_value (xs ys : List Nat) : (natListEqMeter xs ys).value=decide (xs=ys) :=
 list_eq_value natEqMeter (by intros;rfl) xs ys

theorem nat_list_eq_work (xs ys : List Nat) : (natListEqMeter xs ys).work≤3*xs.length+1 :=
 list_eq_work natEqMeter xs ys 1 (by intros;exact Nat.le_refl 1)

def addressListsEqMeter := listEqMeter eqAddressMeter

theorem address_lists_eq_value (xs ys : List RMAF.Vertex) :
 (addressListsEqMeter xs ys).value=decide (xs=ys) := by
 apply list_eq_value
 intro x y
 apply Bool.eq_iff_iff.2
 simp only [eq_address_value,beq_iff_eq,decide_eq_true_eq]

/-- Bounded existential scans left to right and stops at its first witness. -/
def anyMeter {α : Type} (f : α→Measured Bool) : List α→Measured Bool
 | []=>⟨false,1⟩
 | x::xs=>let a:=f x
           if a.value then ⟨true,a.work+1⟩
           else let r:=anyMeter f xs;⟨r.value,a.work+r.work+1⟩

def allMeter {α : Type} (f : α→Measured Bool) : List α→Measured Bool
 | []=>⟨true,1⟩
 | x::xs=>let a:=f x
           if a.value then let r:=allMeter f xs;⟨r.value,a.work+r.work+1⟩
           else ⟨false,a.work+1⟩

theorem any_value {α : Type} (f : α→Measured Bool) (xs : List α) :
 (anyMeter f xs).value=xs.any (fun x=>(f x).value) := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>simp only [anyMeter,List.any_cons];split <;> simp_all

theorem all_value {α : Type} (f : α→Measured Bool) (xs : List α) :
 (allMeter f xs).value=xs.all (fun x=>(f x).value) := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>simp only [allMeter,List.all_cons];split <;> simp_all

theorem any_work {α : Type} (f : α→Measured Bool) (xs : List α) (K : Nat)
 (h : ∀x,x∈xs→(f x).work≤K) : (anyMeter f xs).work≤(K+1)*xs.length+1 := by
 induction xs with
 | nil=>simp [anyMeter]
 | cons x xs ih=>
  have a:=h x (by simp);have r:=ih (by intro y hy;exact h y (by simp [hy]))
  simp only [anyMeter,List.length_cons,Nat.mul_succ]
  split <;> dsimp only <;> omega

theorem all_work {α : Type} (f : α→Measured Bool) (xs : List α) (K : Nat)
 (h : ∀x,x∈xs→(f x).work≤K) : (allMeter f xs).work≤(K+1)*xs.length+1 := by
 induction xs with
 | nil=>simp [allMeter]
 | cons x xs ih=>
  have a:=h x (by simp);have r:=ih (by intro y hy;exact h y (by simp [hy]))
  simp only [allMeter,List.length_cons,Nat.mul_succ]
  split <;> dsimp only <;> omega

/-- Thunks retain the outer conjunction's early refusal order. -/
def checksMeter : List (Unit→Measured Bool)→Measured Bool
 | []=>⟨true,1⟩
 | f::fs=>let a:=f ()
           if a.value then let r:=checksMeter fs;⟨r.value,a.work+r.work+1⟩
           else ⟨false,a.work+1⟩

theorem checks_value (fs : List (Unit→Measured Bool)) :
 (checksMeter fs).value=fs.all (fun f=>(f ()).value) := by
 induction fs with
 | nil=>rfl
 | cons f fs ih=>simp only [checksMeter,List.all_cons];split <;> simp_all

theorem checks_work (fs : List (Unit→Measured Bool)) :
 (checksMeter fs).work≤(fs.map (fun f=>(f ()).work)).sum+fs.length+1 := by
 induction fs with
 | nil=>simp [checksMeter]
 | cons f fs ih=>simp only [checksMeter,List.map_cons,List.sum_cons,List.length_cons];split <;> dsimp only <;> omega

end Universal233.PaidLiteralDecisionWork
