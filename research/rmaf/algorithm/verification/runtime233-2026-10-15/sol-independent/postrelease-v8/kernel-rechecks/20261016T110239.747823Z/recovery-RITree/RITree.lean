import RIBudget
namespace OrdinaryDispatch.RecoveryInitialBits
open RMAF Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits

inductive InputTree where
 | leaf : List Bool→InputTree
 | node : InputTree→InputTree→InputTree
 deriving DecidableEq,Repr
/-- Specification only. -/
def viewInput : InputTree→Tree
 | .leaf x=>.leaf (decode x)
 | .node l r=>.node (viewInput l) (viewInput r)
def inputNodes : InputTree→Nat
 | .leaf _=>1
 | .node l r=>1+inputNodes l+inputNodes r
def inputLeaves : InputTree→List (List Bool)
 | .leaf x=>[x]
 | .node l r=>inputLeaves l++inputLeaves r
def InputWords (W : Nat) : InputTree→Prop
 | .leaf x=>x.length≤W
 | .node l r=>InputWords W l ∧ InputWords W r
@[simp] theorem inputNodes_view (t : InputTree) : treeNodes (viewInput t)=inputNodes t := by induction t <;> simp_all [viewInput,inputNodes,treeNodes]
@[simp] theorem inputLeaves_view (t : InputTree) : (inputLeaves t).map decode=leaves (viewInput t) := by induction t <;> simp_all [viewInput,inputLeaves,leaves,List.map_append]
theorem inputNodes_pos (t : InputTree) : 1≤inputNodes t := by cases t <;> simp [inputNodes];omega

theorem inputLeaves_length (t : InputTree) : (inputLeaves t).length≤inputNodes t := by
 induction t with
 | leaf x=>simp [inputLeaves,inputNodes]
 | node l r il ir=>simp only [inputLeaves,inputNodes,List.length_append];omega
theorem inputLeaves_words (W : Nat) (t : InputTree) (h : InputWords W t) : ∀x∈inputLeaves t,x.length≤W := by
 induction t with
 | leaf x=>simpa [inputLeaves,InputWords] using h
 | node l r il ir=>intro x hx;rcases List.mem_append.mp hx with hx|hx;exact il h.1 x hx;exact ir h.2 x hx

def copyInput : InputTree→Charged InputTree
 | .leaf x=>let r:=copyBits x;⟨.leaf r.value,r.work+4⟩
 | .node l r=>let a:=copyInput l;let b:=copyInput r;⟨.node a.value b.value,a.work+b.work+8⟩
@[simp] theorem copyInput_value (t : InputTree) : (copyInput t).value=t := by induction t <;> simp_all [copyInput]
def closeInput : InputTree→Charged Unit
 | .leaf x=>let r:=closeBits x;⟨(),r.work+4⟩
 | .node l r=>let a:=closeInput l;let b:=closeInput r;⟨(),a.work+b.work+8⟩
theorem copyInput_work (W : Nat) (t : InputTree) (h : InputWords W t) : (copyInput t).work≤16*(W+1)*inputNodes t := by
 induction t with
 | leaf x=>simp only [InputWords] at h;simp only [copyInput,copyBits_work,inputNodes,Nat.mul_one];omega
 | node l r il ir=>have a:=il h.1;have b:=ir h.2;simp only [copyInput,inputNodes,Nat.mul_add,Nat.mul_one] at a b ⊢;omega
theorem closeInput_work (W : Nat) (t : InputTree) (h : InputWords W t) : (closeInput t).work≤16*(W+1)*inputNodes t := by
 induction t with
 | leaf x=>simp only [InputWords] at h;simp only [closeInput,closeBits_work,inputNodes,Nat.mul_one];omega
 | node l r il ir=>have a:=il h.1;have b:=ir h.2;simp only [closeInput,inputNodes,Nat.mul_add,Nat.mul_one] at a b ⊢;omega

def appendRefs {α : Type} : List α→List α→Charged (List α)
 | [],ys=>⟨ys,2⟩
 | x::xs,ys=>let r:=appendRefs xs ys;⟨x::r.value,r.work+4⟩
@[simp] theorem appendRefs_value {α : Type} (xs ys : List α) : (appendRefs xs ys).value=xs++ys := by induction xs <;> simp_all [appendRefs]
@[simp] theorem appendRefs_work {α : Type} (xs ys : List α) : (appendRefs xs ys).work=4*xs.length+2 := by induction xs <;> simp only [appendRefs,List.length_nil,List.length_cons] at * <;> omega

def closeSpine {α : Type} : List α→Charged Unit
 | []=>⟨(),2⟩
 | _::xs=>let r:=closeSpine xs;⟨(),r.work+4⟩
@[simp] theorem closeSpine_work {α : Type} (xs : List α) : (closeSpine xs).work=4*xs.length+2 := by induction xs <;> simp only [closeSpine,List.length_nil,List.length_cons] at * <;> omega

def leafArrays : InputTree→Charged (List (List Bool))
 | .leaf x=>let c:=copyBits x;⟨[c.value],c.work+4⟩
 | .node l r=>let a:=leafArrays l;let b:=leafArrays r;let p:=appendRefs a.value b.value
   let close:=closeSpine a.value
   ⟨p.value,a.work+b.work+p.work+close.work+8⟩
@[simp] theorem leafArrays_value (t : InputTree) : (leafArrays t).value=inputLeaves t := by induction t <;> simp_all [leafArrays,inputLeaves]
theorem leafArrays_work (W N : Nat) (t : InputTree) (h : InputWords W t) (size : inputNodes t≤N) :
 (leafArrays t).work≤32*(W+1)*(N+1)*inputNodes t := by
 induction t with
 | leaf x=>
  simp only [InputWords] at h
  have p:1≤N+1:=by omega
  have scale:=Nat.mul_le_mul_left (32*(W+1)) p
  simp only [leafArrays,copyBits_work,inputNodes,Nat.mul_one] at *
  omega
 | node l r il ir=>
  have ls:inputNodes l≤N:=by simp only [inputNodes] at size;omega
  have rs:inputNodes r≤N:=by simp only [inputNodes] at size;omega
  have a:=il h.1 ls;have b:=ir h.2 rs
  have len:=inputLeaves_length l
  have scale:=Nat.mul_le_mul_right (N+1) (show 32≤32*(W+1) by omega)
  simp only [leafArrays,leafArrays_value,appendRefs_work,closeSpine_work,inputNodes,Nat.mul_add,Nat.mul_one] at a b scale ⊢
  omega

def appendAddress : List Bool→Bool→Charged (List Bool)
 | [],b=>⟨[b],4⟩
 | x::xs,b=>let r:=appendAddress xs b;⟨x::r.value,r.work+4⟩
@[simp] theorem appendAddress_value (p : List Bool) (b : Bool) : (appendAddress p b).value=p++[b] := by induction p <;> simp_all [appendAddress]
@[simp] theorem appendAddress_work (p : List Bool) (b : Bool) : (appendAddress p b).work=4*(p.length+1) := by induction p <;> simp only [appendAddress,List.length_nil,List.length_cons] at * <;> omega
end OrdinaryDispatch.RecoveryInitialBits
