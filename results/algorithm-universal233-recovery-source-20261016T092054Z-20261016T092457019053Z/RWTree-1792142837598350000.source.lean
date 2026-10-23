import OWBudgets
namespace OrdinaryDispatch.RecoveryLocalWork
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.OptimizerLocalWork
set_option maxRecDepth 16000

/-- Actual groups append copies the left group list. -/
def meterGroups : GTree→Charged (List Group)
 | .leaf g=>⟨[g],4⟩
 | .node _ l r=>let a:=meterGroups l;let b:=meterGroups r
   ⟨a.value++b.value,a.work+b.work+4*(a.value.length+1)+4⟩
@[simp] theorem meterGroups_value (t : GTree) : (meterGroups t).value=groups t := by
 induction t <;> simp_all [meterGroups,groups]
theorem meterGroups_bound (t : GTree) (N : Nat) (size : footprint t≤N) :
 (meterGroups t).work≤16*(N+1)*footprint t := by
 induction t with
 | leaf g=>simp only [meterGroups,footprint,Nat.mul_add,Nat.mul_one];omega
 | node p l r il ir=>
  have ls:footprint l≤N:=by simp only [footprint] at size;omega
  have rs:footprint r≤N:=by simp only [footprint] at size;omega
  have a:=il ls;have b:=ir rs;have len:=groups_length l
  simp only [meterGroups,meterGroups_value,footprint,Nat.mul_add,Nat.mul_one];omega

def normalizeFee : GTree→GTree→Nat
 | .leaf a,.leaf _=>4*(a.labels.length+1)+12
 | _,_=>8

def meterNormalize : GTree→Charged GTree
 | .leaf g=>⟨.leaf g,4⟩
 | .node p l r=>let a:=meterNormalize l;let b:=meterNormalize r
   ⟨match a.value,b.value with
    | .leaf x,.leaf y=>if x.color=y.color then .leaf ⟨p,x.labels++y.labels,x.color⟩ else .node p (.leaf x) (.leaf y)
    | x,y=>.node p x y,
    a.work+b.work+normalizeFee a.value b.value⟩
@[simp] theorem meterNormalize_value (t : GTree) : (meterNormalize t).value=normalize t := by
 induction t <;> simp_all only [meterNormalize,normalize]

theorem normalizeFee_bound (l r : GTree) (N : Nat) (size : footprint l≤N) :
 normalizeFee l r≤16*(N+1) := by cases l <;> cases r <;> simp_all [normalizeFee,footprint] <;> omega

theorem meterNormalize_bound (t : GTree) (N : Nat) (size : footprint t≤N) :
 (meterNormalize t).work≤32*(N+1)*footprint t := by
 induction t with
 | leaf g=>simp only [meterNormalize,footprint,Nat.mul_add,Nat.mul_one];omega
 | node p l r il ir=>
  have ls:footprint l≤N:=by simp only [footprint] at size;omega
  have rs:footprint r≤N:=by simp only [footprint] at size;omega
  have a:=il ls;have b:=ir rs
  have f:=normalizeFee_bound (normalize l) (normalize r) N (Nat.le_trans (normalize_footprint l) ls)
  simp only [meterNormalize,meterNormalize_value,footprint,Nat.mul_add,Nat.mul_one];omega

/-- Both recursive subtrees may be conservatively charged even when the source
root-address guard stops early. Every actual address comparison is expanded. -/
def meterErase (chosen : RMAF.Vertex) : GTree→Charged (Option GTree)
 | .leaf g=>let e:=meterAddressEq g.origin chosen
   ⟨if e.value then none else some (.leaf g),e.work+8⟩
 | .node p l r=>let e:=meterAddressEq p chosen;let a:=meterErase chosen l;let b:=meterErase chosen r
   ⟨if e.value then none else match a.value,b.value with
    | none,none=>none | some x,none=>some x | none,some y=>some y | some x,some y=>some (.node p x y),
    e.work+a.work+b.work+12⟩
@[simp] theorem meterErase_value (chosen : RMAF.Vertex) (t : GTree) :
 (meterErase chosen t).value=CoreProgram.erase chosen t := by
 induction t with
 | leaf g=>by_cases h:g.origin=chosen <;> simp [meterErase,CoreProgram.erase,h]
 | node p l r il ir=>by_cases h:p=chosen <;> simp [meterErase,CoreProgram.erase,h,il,ir]

theorem meterErase_bound (chosen : RMAF.Vertex) (t : GTree) (N : Nat) (size : footprint t≤N) :
 (meterErase chosen t).work≤32*(N+1)*footprint t := by
 induction t with
 | leaf g=>
  have e:=meterAddressEq_bound g.origin chosen
  simp only [meterErase,footprint,Nat.mul_add,Nat.mul_one] at *;omega
 | node p l r il ir=>
  have ls:footprint l≤N:=by simp only [footprint] at size;omega
  have rs:footprint r≤N:=by simp only [footprint] at size;omega
  have a:=il ls;have b:=ir rs;have e:=meterAddressEq_bound p chosen
  simp only [meterErase,footprint,Nat.mul_add,Nat.mul_one] at *;omega

def meterMixed : GTree→Charged (Option (Group×Group))
 | .leaf _=>⟨none,2⟩
 | .node _ l r=>let a:=meterMixed l;let b:=meterMixed r
   ⟨match l,r with | .leaf x,.leaf y=>some (x,y) | _,_=>a.value.or b.value,a.work+b.work+8⟩
@[simp] theorem meterMixed_value (t : GTree) : (meterMixed t).value=mixedCherry t := by
 induction t with
 | leaf g=>rfl
 | node p l r il ir=>cases l <;> cases r <;> simp_all [meterMixed,mixedCherry]
theorem meterMixed_bound (t : GTree) : (meterMixed t).work≤8*footprint t := by
 induction t <;> simp_all only [meterMixed,footprint,Nat.mul_add,Nat.mul_one] <;> omega

end OrdinaryDispatch.RecoveryLocalWork
