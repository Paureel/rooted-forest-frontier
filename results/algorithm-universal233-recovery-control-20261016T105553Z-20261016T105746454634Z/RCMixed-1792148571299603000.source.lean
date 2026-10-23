import RCFilter
namespace OrdinaryDispatch.RecoveryControlBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits

abbrev GroupPair := BitGroup×BitGroup

def closePair (p : GroupPair) : Charged Unit :=
 let a:=closeGroup p.1;let b:=closeGroup p.2;⟨(),a.work+b.work+8⟩
def closeMaybePair : Option GroupPair→Charged Unit
 | none=>⟨(),2⟩
 | some p=>let r:=closePair p;⟨(),r.work+4⟩
def pickPair (a b : Option GroupPair) : Charged (Option GroupPair) :=
 match a with
 | none=>⟨b,8⟩
 | some p=>let c:=closeMaybePair b;⟨some p,c.work+8⟩
@[simp] theorem pickPair_value (a b : Option GroupPair) : (pickPair a b).value=a.or b := by cases a <;> rfl

def rawMixed : BitTree→Option GroupPair
 | .leaf _=>none
 | .node _ (.leaf a) (.leaf b)=>some (a,b)
 | .node _ l r=>(rawMixed l).or (rawMixed r)

def mixedBits : BitTree→Charged (Option GroupPair)
 | .leaf _=>⟨none,4⟩
 | .node _ (.leaf a) (.leaf b)=>let x:=copyGroup a;let y:=copyGroup b;⟨some (x.value,y.value),x.work+y.work+8⟩
 | .node _ l r=>let a:=mixedBits l;let b:=mixedBits r;let c:=pickPair a.value b.value
   ⟨c.value,a.work+b.work+c.work+8⟩
@[simp] theorem mixedBits_value (t : BitTree) : (mixedBits t).value=rawMixed t := by
 induction t with
 | leaf g=>rfl
 | node p l r il ir=>cases l <;> cases r <;> simp_all [mixedBits,rawMixed]

def viewPair (p : GroupPair) : Group×Group := (viewGroup p.1,viewGroup p.2)
theorem pairMap_or (a b : Option GroupPair) : (a.or b).map viewPair=(a.map viewPair).or (b.map viewPair) := by cases a <;> rfl
@[simp] theorem rawMixed_view (t : BitTree) : (rawMixed t).map viewPair=mixedCherry (viewTree t) := by
 induction t with
 | leaf g=>rfl
 | node p l r il ir=>cases l <;> cases r <;> simp_all [rawMixed,viewTree,mixedCherry,viewPair,pairMap_or]

theorem or_some {α : Type} (a b : Option α) (x : α) (h : a.or b=some x) : a=some x ∨ b=some x := by
 cases a with
 | none=>exact Or.inr h
 | some y=>exact Or.inl h

theorem rawMixed_mem (t : BitTree) (a b : BitGroup) (h : rawMixed t=some (a,b)) : a∈rawGroups t ∧ b∈rawGroups t := by
 induction t with
 | leaf g=>simp [rawMixed] at h
 | node p l r il ir=>
  have fallback (h : (rawMixed l).or (rawMixed r)=some (a,b)) :
   a∈rawGroups (.node p l r) ∧ b∈rawGroups (.node p l r):=by
   rcases or_some _ _ _ h with h|h
   · have m:=il h;exact ⟨List.mem_append_left _ m.1,List.mem_append_left _ m.2⟩
   · have m:=ir h;exact ⟨List.mem_append_right _ m.1,List.mem_append_right _ m.2⟩
  cases l with
  | leaf x=>
   cases r with
   | leaf y=>simp only [rawMixed,Option.some.injEq,Prod.mk.injEq] at h
             obtain ⟨ha,hb⟩:=h;subst a;subst b;simp [rawGroups]
   | node q x y=>exact fallback h
  | node q x y=>exact fallback h

theorem mixedBits_caps (W N : Nat) (t : BitTree) (words : TreeWords W t) (size : footprint (viewTree t)≤N)
 (a b : BitGroup) (h : (mixedBits t).value=some (a,b)) : GroupCap W N a ∧ GroupCap W N b := by
 have caps:=rawGroups_caps W N t words size
 have mem:=rawMixed_mem t a b (by simpa using h)
 exact ⟨caps a mem.1,caps b mem.2⟩

theorem closeMaybePair_work (W N : Nat) (p : Option GroupPair)
 (caps : ∀a b,p=some (a,b)→GroupCap W N a ∧ GroupCap W N b) :
 (closeMaybePair p).work≤3*groupFee W N := by
 have pos:=groupFee_positive W N
 cases p with
 | none=>simp only [closeMaybePair];omega
 | some p=>
  have cs:=caps p.1 p.2 rfl
  have a:=closed_group_fee W N p.1 cs.1;have b:=closed_group_fee W N p.2 cs.2
  simp only [closeMaybePair,closePair];omega

theorem pickPair_work (W N : Nat) (a b : Option GroupPair)
 (caps : ∀x y,b=some (x,y)→GroupCap W N x ∧ GroupCap W N y) :
 (pickPair a b).work≤4*groupFee W N := by
 have pos:=groupFee_positive W N
 have c:=closeMaybePair_work W N b caps
 cases a <;> simp only [pickPair] <;> omega

theorem mixedBits_work_nodes (W N : Nat) (t : BitTree) (words : TreeWords W t) (size : footprint (viewTree t)≤N) :
 (mixedBits t).work≤8*groupFee W N*bitNodes t := by
 have pos:=groupFee_positive W N
 induction t with
 | leaf g=>simp only [mixedBits,bitNodes,Nat.mul_one];omega
 | node p l r il ir=>
  have ls:footprint (viewTree l)≤N:=by simp only [viewTree,footprint] at size;omega
  have rs:footprint (viewTree r)≤N:=by simp only [viewTree,footprint] at size;omega
  have a:=il words.1 ls;have b:=ir words.2 rs
  have pick:=pickPair_work W N (mixedBits l).value (mixedBits r).value
   (by intro x y h;exact mixedBits_caps W N r words.2 rs x y h)
  have expand (A l r : Nat) : A*(1+l+r)=A*l+A*r+A:=by simp only [Nat.mul_add,Nat.mul_one];omega
  have fallback : (mixedBits l).work+(mixedBits r).work+(pickPair (mixedBits l).value (mixedBits r).value).work+8≤8*groupFee W N*(1+bitNodes l+bitNodes r):=by
   rw [expand];omega
  cases l with
  | leaf x=>
   cases r with
   | leaf y=>
    have xcap:GroupCap W N x:=⟨words.1.1,words.1.2,ls⟩
    have ycap:GroupCap W N y:=⟨words.2.1,words.2.2,rs⟩
    have cx:=copied_group_fee W N x xcap;have cy:=copied_group_fee W N y ycap
    simp only [mixedBits,bitNodes,Nat.mul_one];omega
   | node q x y=>exact fallback
  | node q x y=>exact fallback

theorem mixedBits_work (W N : Nat) (t : BitTree) (words : TreeWords W t) (size : footprint (viewTree t)≤N) :
 (mixedBits t).work≤8*groupFee W N*N :=
 Nat.le_trans (mixedBits_work_nodes W N t words size)
  (Nat.mul_le_mul_left (8*groupFee W N) (Nat.le_trans (bitNodes_footprint t) size))
end OrdinaryDispatch.RecoveryControlBits
