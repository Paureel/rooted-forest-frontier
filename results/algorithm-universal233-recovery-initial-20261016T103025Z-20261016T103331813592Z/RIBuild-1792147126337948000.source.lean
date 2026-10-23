import RITree
namespace OrdinaryDispatch.RecoveryInitialBits
open RMAF Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits

def build (P : List (List (List Bool))) (p : List Bool) : InputTree→Charged BitTree
 | .leaf x=>let l:=copyBits x;let a:=copyBits p;let c:=ownedColor P x
   ⟨.leaf ⟨a.value,[l.value],c.value⟩,l.work+a.work+c.work+12⟩
 | .node l r=>
   let pl:=appendAddress p false;let pr:=appendAddress p true
   let a:=build P pl.value l;let b:=build P pr.value r;let own:=copyBits p
   let cl:=closeBits pl.value;let cr:=closeBits pr.value
   ⟨.node own.value a.value b.value,a.work+b.work+pl.work+pr.work+own.work+cl.work+cr.work+12⟩

@[simp] theorem build_value (P : List (List (List Bool))) (p : List Bool) (t : InputTree) :
 viewTree (build P p t).value=fromTree (FinalCutRecovery.blockColor (P.map (List.map decode))) p (viewInput t) := by
 induction t generalizing p <;> simp_all [build,viewTree,viewGroup,fromTree,viewInput]

theorem build_words (W : Nat) (P : List (List (List Bool))) (p : List Bool) (t : InputTree)
 (tw : InputWords W t) (pw : ForestWords W P) : TreeWords W (build P p t).value := by
 induction t generalizing p with
 | leaf x=>
  have color:=ownedColor_length W P x pw
  simpa [build,TreeWords,InputWords] using And.intro tw color
 | node l r il ir=>exact ⟨il _ tw.1,ir _ tw.2⟩

/-- A derived helper envelope; build's runtime work is the operation sum above. -/
def buildCap (W N : Nat) (P : List (List (List Bool))) : Nat :=
 160*(W+1)*(P.flatten.length+P.length+1)+64*(W+1)*(N+1)

theorem build_work (W N : Nat) (P : List (List (List Bool))) (p : List Bool) (t : InputTree)
 (tw : InputWords W t) (pw : ForestWords W P) (size : p.length+inputNodes t≤N) :
 (build P p t).work≤buildCap W N P*inputNodes t := by
 have dW:64*(W+1)≤64*(W+1)*(N+1):=by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (64*(W+1)) (show 1≤N+1 by omega)
 have dN:64*(N+1)≤64*(W+1)*(N+1):=Nat.mul_le_mul_right (N+1) (by omega)
 induction t generalizing p with
 | leaf x=>
  have color:=ownedColor_work W P x tw pw
  simp only [InputWords] at tw
  simp only [inputNodes] at size
  simp only [build,copyBits_work,inputNodes,Nat.mul_one,buildCap]
  omega
 | node l r il ir=>
  have ls:(p++[false]).length+inputNodes l≤N:=by simp only [inputNodes,List.length_append,List.length_singleton] at size ⊢;omega
  have rs:(p++[true]).length+inputNodes r≤N:=by simp only [inputNodes,List.length_append,List.length_singleton] at size ⊢;omega
  have a:=il _ tw.1 ls;have b:=ir _ tw.2 rs
  have pn:p.length≤N:=by simp only [inputNodes] at size;omega
  have fee: (appendAddress p false).work+(appendAddress p true).work+(copyBits p).work+
   (closeBits (appendAddress p false).value).work+(closeBits (appendAddress p true).value).work+12≤buildCap W N P:=by
   simp only [appendAddress_work,copyBits_work,closeBits_work,appendAddress_value,List.length_append,List.length_singleton,buildCap]
   omega
  have expand (A l r : Nat) : A*(1+l+r)=A*l+A*r+A:=by simp only [Nat.mul_add,Nat.mul_one];omega
  simp only [build,appendAddress_value,inputNodes,expand]
  omega
end OrdinaryDispatch.RecoveryInitialBits
