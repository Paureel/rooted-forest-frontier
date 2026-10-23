import IncidentWork
import FinalSelector
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching

def subtreeMeter : Tree→RMAF.Vertex→Measured (Option Tree)
 | T,[]=>⟨some T,1⟩
 | .leaf _,_::_=>⟨none,1⟩
 | .node l r,s::p=>let m:=subtreeMeter (if s then r else l) p;⟨m.value,m.work+2⟩

theorem subtree_value (T : Tree) (p : RMAF.Vertex) : (subtreeMeter T p).value=subtree T p := by
 induction p generalizing T with
 | nil=>rfl
 | cons s p ih=>cases T with
  | leaf x=>rfl
  | node l r=>simp only [subtreeMeter,subtree,ih]

theorem subtree_work (T : Tree) (p : RMAF.Vertex) : (subtreeMeter T p).work≤2*p.length+1 := by
 induction p generalizing T with
 | nil=>simp [subtreeMeter]
 | cons s p ih=>cases T with
  | leaf x=>simp [subtreeMeter]
  | node l r=>have:=ih (if s then r else l);simp only [subtreeMeter,List.length_cons];omega

/-- Full filterMap retains every visited failed and duplicate occurrence.
The receipt append itself is charged at the length of its left list. -/
def optionsMeter {α β : Type} (f : α→CheckReceipt (Option β)) : List α→CheckReceipt (List β)
 | []=>⟨[],1,[]⟩
 | x::xs=>let a:=f x;let r:=optionsMeter f xs
           ⟨match a.value with | some y=>y::r.value | none=>r.value,
            a.work+r.work+a.calls.length+3,a.calls++r.calls⟩

theorem options_value {α β : Type} (f : α→CheckReceipt (Option β)) (xs : List α) :
 (optionsMeter f xs).value=xs.filterMap (fun x=>(f x).value) := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>simp only [optionsMeter,List.filterMap_cons,ih];split <;> rfl

theorem options_work {α β : Type} (f : α→CheckReceipt (Option β)) (xs : List α) (B C : Nat)
 (caps : ∀x,x∈xs →(f x).work≤B ∧ (f x).calls.length≤C) :
 (optionsMeter f xs).work≤(B+C+3)*xs.length+1 := by
 induction xs with
 | nil=>simp [optionsMeter]
 | cons x xs ih=>
  have a:=caps x (by simp)
  have tail:=ih (fun y hy=>caps y (by simp [hy]))
  simp only [optionsMeter,List.length_cons,Nat.mul_succ]
  omega

theorem options_calls_count {α β : Type} (f : α→CheckReceipt (Option β)) (xs : List α) (C : Nat)
 (caps : ∀x,x∈xs →(f x).calls.length≤C) :
 (optionsMeter f xs).calls.length≤C*xs.length := by
 induction xs with
 | nil=>simp [optionsMeter]
 | cons x xs ih=>
  have a:=caps x (by simp)
  have tail:=ih (fun y hy=>caps y (by simp [hy]))
  simp only [optionsMeter,List.length_append,List.length_cons,Nat.mul_succ]
  omega

theorem options_call {α β : Type} (f : α→CheckReceipt (Option β)) (xs : List α)
 {r : CheckRequest} (mem : r∈(optionsMeter f xs).calls) :
 ∃x,x∈xs ∧ r∈(f x).calls := by
 induction xs with
 | nil=>simp [optionsMeter] at mem
 | cons x xs ih=>
  simp only [optionsMeter,List.mem_append] at mem
  rcases mem with h|h
  · exact ⟨x,by simp,h⟩
  · obtain ⟨y,hy,hr⟩:=ih h;exact ⟨y,by simp [hy],hr⟩

theorem options_count {α β : Type} (f : α→CheckReceipt (Option β)) (xs : List α) :
 (optionsMeter f xs).value.length≤xs.length := by
 rw [options_value]
 exact List.length_filterMap_le _ _

def paintMeter (T : Tree) (X : List Nat) (q : RMAF.Vertex) : Measured Bool :=
 let m:=minimalMeter X T;let c:=containsAddressMeter q m.value
 ⟨c.value,m.work+c.work+1⟩

theorem paint_value (T : Tree) (X : List Nat) (q : RMAF.Vertex) :
 (paintMeter T X q).value=Rule5Local.paint T X q := by
 simp only [paintMeter,contains_address_value,minimal_value,Rule5Local.paint]

def paintBudget (k n : Nat) :=minimalBudget k n+(2*n+2)*(2*n)+2

theorem paint_work (T : Tree) (X : List Nat) (q : RMAF.Vertex) (cap : q.length≤(leaves T).length) :
 (paintMeter T X q).work≤paintBudget X.length (leaves T).length := by
 have m:=minimal_work X T
 have mc:=minimal_count X T
 have vc:=vertices_count T
 have ml : (minimalMeter X T).value.length≤2*(leaves T).length := by rw [minimal_value];omega
 have ca:=contains_address_work q (minimalMeter X T).value (leaves T).length cap (by
  intro p hp;have:=minimal_address X T hp;omega)
 have slots:=Nat.mul_le_mul_left (2*(leaves T).length+2) ml
 simp only [paintMeter,paintBudget]
 omega

def outsideCheckMeter (T : Tree) (X : List Nat) (q : RMAF.Vertex) (x : Nat) : Measured Bool :=
 let l:=subtreeLabelsMeter T q;let c:=containsMeter x l.value;let p:=paintMeter T X q
 ⟨c.value!=p.value,l.work+c.work+p.work+2⟩

theorem outside_check_value (T : Tree) (X : List Nat) (q : RMAF.Vertex) (x : Nat) :
 (outsideCheckMeter T X q x).value=Rule5FinalClassification.outsideCheck T X q x := by
 simp only [outsideCheckMeter,Rule5FinalClassification.outsideCheck,subtree_labels_value,contains_value,paint_value]

def outsideCheckBudget (k n : Nat) :=4*n*n+4*n+paintBudget k n+5

theorem outside_check_work (T : Tree) (X : List Nat) (q : RMAF.Vertex) (x : Nat)
 (cap : q.length≤(leaves T).length) :
 (outsideCheckMeter T X q x).work≤outsideCheckBudget X.length (leaves T).length := by
 have l:=subtree_labels_work T q
 have dom:=subtree_labels_payload T q
 have c:=contains_work x (subtreeLabelsMeter T q).value
 have p:=paint_work T X q cap
 simp only [outsideCheckMeter,outsideCheckBudget]
 omega
end Universal233.Rule5PendantLocalWork
