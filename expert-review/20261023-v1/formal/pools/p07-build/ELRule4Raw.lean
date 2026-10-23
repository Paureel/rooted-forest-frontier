import ELRule4Guards
namespace OrdinaryDispatch.EarlyLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence
set_option maxRecDepth 12000

theorem double_power (k N p : Nat) : k*(N+1)^p*(2*(N+1))=(2*k)*(N+1)^(p+1) := by
 rw [Nat.pow_succ]
 ac_rfl

def meterFlatMap {α β : Type} (f : α→Charged (List β)) : List α→Charged (List β)
 | []=>⟨[],1⟩
 | x::xs=>let a:=f x;let r:=meterFlatMap f xs;⟨a.value++r.value,a.work+r.work+6*(a.value.length+1)⟩
@[simp] theorem meterFlatMap_value {α β : Type} (f : α→Charged (List β)) (xs : List α) :
 (meterFlatMap f xs).value=xs.flatMap (fun x=>(f x).value) := by induction xs <;> simp_all [meterFlatMap]
theorem meterFlatMap_bound {α β : Type} (f : α→Charged (List β)) (xs : List α) (A C : Nat)
 (work : ∀x∈xs,(f x).work≤A) (size : ∀x∈xs,(f x).value.length≤C) :
 (meterFlatMap f xs).work≤(A+6*(C+1))*(xs.length+1) := by
 induction xs with
 | nil=>simp [meterFlatMap];omega
 | cons x xs ih=>
  have a:=work x (by simp);have al:=size x (by simp)
  have b:=ih (fun y hy=>work y (by simp [hy])) (fun y hy=>size y (by simp [hy]))
  simp only [meterFlatMap,List.length_cons,Nat.mul_add,Nat.mul_one] at *;omega

theorem flatMap_length_cap {α β : Type} (f : α→List β) (xs : List α) (C : Nat)
 (size : ∀x∈xs,(f x).length≤C) : (xs.flatMap f).length≤C*xs.length := by
 induction xs with
 | nil=>simp
 | cons x xs ih=>
  have a:=size x (by simp);have b:=ih (fun y hy=>size y (by simp [hy]))
  simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one];omega

def meterRawR (S : Tree) (ab ac : Nat×Nat) (q : RMAF.Vertex) : Charged (List Rule4.RawChoice) :=
 let p:=meterPendant S ab.1 ab.2
 let m:=meterMap (fun r=>⟨(⟨ab.1,ab.2,ac.2,q,r⟩:Rule4.RawChoice),4⟩) p.value
 ⟨m.value,p.work+m.work+2⟩
@[simp] theorem meterRawR_value (S ab ac q) : (meterRawR S ab ac q).value=
 (HardParent.pendantOriginal S ab.1 ab.2).map (fun r=>(⟨ab.1,ab.2,ac.2,q,r⟩:Rule4.RawChoice)) := by simp [meterRawR]

def meterRawAC (S : Tree) (ab ac : Nat×Nat) : Charged (List Rule4.RawChoice) :=
 let test:=meterPendant S ab.1 ab.2
 if ab.1=ac.1 ∧ test.value.length=2 then
  let p:=meterPendant S ab.1 ab.2
  let f:=meterFlatMap (meterRawR S ab ac) p.value
  ⟨f.value,test.work+4*(test.value.length+1)+p.work+f.work+8⟩
 else ⟨[],test.work+4*(test.value.length+1)+4⟩
@[simp] theorem meterRawAC_value (S ab ac) : (meterRawAC S ab ac).value=
 (if ab.1=ac.1 ∧ (HardParent.pendantOriginal S ab.1 ab.2).length=2 then
  (HardParent.pendantOriginal S ab.1 ab.2).flatMap (fun q=>
    (HardParent.pendantOriginal S ab.1 ab.2).map (fun r=>(⟨ab.1,ab.2,ac.2,q,r⟩:Rule4.RawChoice))) else []) := by
 simp only [meterRawAC,meterPendant_value,meterFlatMap_value,meterRawR_value]
 split <;> rfl

theorem rawAC_length (S : Tree) (ab ac : Nat×Nat) : (meterRawAC S ab ac).value.length≤4 := by
 rw [meterRawAC_value]
 split
 · rename_i h
   have len:=(h.2)
   have f:=flatMap_length_cap (fun q=>(HardParent.pendantOriginal S ab.1 ab.2).map (fun r=>(⟨ab.1,ab.2,ac.2,q,r⟩:Rule4.RawChoice)))
    (HardParent.pendantOriginal S ab.1 ab.2) 2 (by intro q hq;simpa [len])
   simpa [len] using f
 · simp

theorem meterRawAC_bound (S : Tree) (ab ac : Nat×Nat) (N : Nat) (sn : treeNodes S≤N) :
 (meterRawAC S ab ac).work≤4096*(N+1)^4 := by
 have p:=meterPendant_bound S ab.1 ab.2 N sn
 have pl:=pendant_length S ab.1 ab.2
 have pow : N+1≤(N+1)^4:=by simpa using pow_mono N 1 4 (by decide)
 have pos : 1≤(N+1)^4:=Nat.one_le_pow _ _ (by omega)
 simp only [meterRawAC,meterPendant_value]
 split
 · rename_i h
   have len:=(h.2)
   have rpoint (q : RMAF.Vertex) : (meterRawR S ab ac q).work≤512*(N+1)^4+26 := by
    have m:=meterMap_bound (fun r=>⟨(⟨ab.1,ab.2,ac.2,q,r⟩:Rule4.RawChoice),4⟩)
     (HardParent.pendantOriginal S ab.1 ab.2) 4 (by intro _ _;exact Nat.le_refl _)
    rw [len] at m
    simp only [meterRawR,meterPendant_value];omega
   have rlen (q : RMAF.Vertex) : (meterRawR S ab ac q).value.length≤2:=by simp [len]
   have flat:=meterFlatMap_bound (meterRawR S ab ac) (HardParent.pendantOriginal S ab.1 ab.2)
    (512*(N+1)^4+26) 2 (fun q _=>rpoint q) (fun q _=>rlen q)
   rw [len] at flat
   simp only [Nat.mul_add,Nat.mul_one] at flat
   simp only [Charged.work]
   omega
 · simp only [Charged.work];omega

def meterRawAB (S : Tree) (ab : Nat×Nat) : Charged (List Rule4.RawChoice) :=
 let c:=meterOrderedCherries S;let m:=meterFlatMap (meterRawAC S ab) c.value
 ⟨m.value,c.work+m.work+2⟩
@[simp] theorem meterRawAB_value (S ab) : (meterRawAB S ab).value=
 (Rule4.orderedCherries S).flatMap (fun ac=>(meterRawAC S ab ac).value) := by simp [meterRawAB]

theorem rawAB_length (S : Tree) (ab : Nat×Nat) :
 (meterRawAB S ab).value.length≤4*(Rule4.orderedCherries S).length := by
 rw [meterRawAB_value]
 exact flatMap_length_cap _ _ 4 (fun ac _=>rawAC_length S ab ac)

theorem meterRawAB_bound (S : Tree) (ab : Nat×Nat) (N : Nat) (sn : treeNodes S≤N) :
 (meterRawAB S ab).work≤16384*(N+1)^5 := by
 have c:=cap_lift N 32 2 5 _ (meterOrderedCherries_bound S N sn) (by decide)
 have cl:=orderedCherries_length S
 have f:=meterFlatMap_bound (meterRawAC S ab) (Rule4.orderedCherries S) (4096*(N+1)^4) 4
  (fun ac _=>meterRawAC_bound S ab ac N sn) (fun ac _=>rawAC_length S ab ac)
 have pos : 1≤(N+1)^4:=Nat.one_le_pow _ _ (by omega)
 have coeff : 4096*(N+1)^4+6*(4+1)≤4126*(N+1)^4:=by omega
 have scale:=Nat.mul_le_mul coeff (show (Rule4.orderedCherries S).length+1≤2*(N+1) by omega)
 have ff : (meterFlatMap (meterRawAC S ab) (Rule4.orderedCherries S)).work≤8252*(N+1)^5:=
  Nat.le_trans f (by simpa only [double_power] using scale)
 have pp : 1≤(N+1)^5:=Nat.one_le_pow _ _ (by omega)
 simp only [meterRawAB,meterOrderedCherries_value];omega

def meterRawChoices (T S : Tree) : Charged (List Rule4.RawChoice) :=
 let c:=meterOrderedCherries T;let m:=meterFlatMap (meterRawAB S) c.value
 ⟨m.value,c.work+m.work+2⟩
@[simp] theorem meterRawChoices_value (T S) : (meterRawChoices T S).value=Rule4.rawChoices T S := by
 simp [meterRawChoices,Rule4.rawChoices]

theorem rawChoices_length (T S : Tree) (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (Rule4.rawChoices T S).length≤16*(N+1)^2 := by
 have tl:=orderedCherries_length T;have sl:=orderedCherries_length S
 have f:=flatMap_length_cap (fun ab=>(meterRawAB S ab).value) (Rule4.orderedCherries T)
   (4*(Rule4.orderedCherries S).length) (fun ab _=>rawAB_length S ab)
 have prod:=Nat.mul_le_mul (show 4*(Rule4.orderedCherries S).length≤8*(N+1) by omega)
   (show (Rule4.orderedCherries T).length≤2*(N+1) by omega)
 have eq : (Rule4.rawChoices T S).length≤(4*(Rule4.orderedCherries S).length)*(Rule4.orderedCherries T).length := by
  simpa [←meterRawChoices_value,meterRawChoices,meterFlatMap_value] using f
 have peq : (8*(N+1))*(2*(N+1))=16*(N+1)^2 := by
  rw [Nat.pow_two]
  change (8*(N+1))*(2*(N+1))=(8*2)*((N+1)*(N+1))
  ac_rfl
 rw [peq] at prod
 exact Nat.le_trans eq prod

theorem meterRawChoices_bound (T S : Tree) (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterRawChoices T S).work≤65536*(N+1)^6 := by
 have c:=cap_lift N 32 2 6 _ (meterOrderedCherries_bound T N tn) (by decide)
 have tl:=orderedCherries_length T;have sl:=orderedCherries_length S
 have f:=meterFlatMap_bound (meterRawAB S) (Rule4.orderedCherries T) (16384*(N+1)^5) (8*(N+1))
  (fun ab _=>meterRawAB_bound S ab N sn) (fun ab _=>Nat.le_trans (rawAB_length S ab) (by omega))
 have p1 : N+1≤(N+1)^5:=by simpa using pow_mono N 1 5 (by decide)
 have pos : 1≤(N+1)^5:=Nat.one_le_pow _ _ (by omega)
 have coeff : 16384*(N+1)^5+6*(8*(N+1)+1)≤16438*(N+1)^5:=by omega
 have scale:=Nat.mul_le_mul coeff (show (Rule4.orderedCherries T).length+1≤2*(N+1) by omega)
 have ff : (meterFlatMap (meterRawAB S) (Rule4.orderedCherries T)).work≤32876*(N+1)^6:=
  Nat.le_trans f (by simpa only [double_power] using scale)
 have pp : 1≤(N+1)^6:=Nat.one_le_pow _ _ (by omega)
 simp only [meterRawChoices,meterOrderedCherries_value];omega

/-- Raw heads are actual source vertices, before any LocalGuard succeeds. -/
theorem rawChoice_head (T S : Tree) (raw : Rule4.RawChoice) (h : raw∈Rule4.rawChoices T S) : raw.cHead.length≤treeNodes S := by
 unfold Rule4.rawChoices at h
 obtain ⟨ab,hab,h⟩:=List.mem_flatMap.1 h
 obtain ⟨ac,hac,h⟩:=List.mem_flatMap.1 h
 split at h
 · obtain ⟨q,hq,h⟩:=List.mem_flatMap.1 h
   obtain ⟨r,hr,eq⟩:=List.mem_map.1 h
   subst raw
   exact pendant_address S ab.1 ab.2 q hq
 · simp at h

end OrdinaryDispatch.EarlyLocalWork
