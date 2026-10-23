import RCAddress
namespace OrdinaryDispatch.RecoveryControlBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits

def eraseBits (chosen : List Bool) : BitTree→Charged (Option BitTree)
 | .leaf g=>let e:=ownedAddressEqual g.origin chosen
   if e.value then ⟨none,e.work+8⟩ else let c:=copyGroup g;⟨some (.leaf c.value),e.work+c.work+8⟩
 | .node p l r=>let e:=ownedAddressEqual p chosen
   if e.value then ⟨none,e.work+8⟩ else
    let a:=eraseBits chosen l;let b:=eraseBits chosen r
    match a.value,b.value with
    | none,none=>⟨none,e.work+a.work+b.work+8⟩
    | some x,none=>⟨some x,e.work+a.work+b.work+8⟩
    | none,some y=>⟨some y,e.work+a.work+b.work+8⟩
    | some x,some y=>let path:=copyBits p;⟨some (.node path.value x y),e.work+a.work+b.work+path.work+12⟩

@[simp] theorem eraseBits_value (chosen : List Bool) (t : BitTree) :
 (eraseBits chosen t).value.map viewTree=CoreProgram.erase chosen (viewTree t) := by
 induction t with
 | leaf g=>simp [eraseBits,CoreProgram.erase,viewTree,viewGroup]
 | node p l r il ir=>
  by_cases eq:p=chosen
  · simp [eraseBits,CoreProgram.erase,viewTree,eq]
  · cases hl:(eraseBits chosen l).value <;> cases hr:(eraseBits chosen r).value <;>
     simp [eraseBits,CoreProgram.erase,viewTree,eq,hl,hr,←il,←ir]

theorem eraseBits_words (W : Nat) (chosen : List Bool) (t out : BitTree) (words : TreeWords W t)
 (h : (eraseBits chosen t).value=some out) : TreeWords W out := by
 induction t generalizing out with
 | leaf g=>
  simp only [eraseBits] at h
  split at h
  · contradiction
  · simp only [copyGroup_value,Option.some.injEq] at h;subst out;exact words
 | node p l r il ir=>
  simp only [eraseBits] at h
  split at h
  · contradiction
  · cases hl:(eraseBits chosen l).value <;> cases hr:(eraseBits chosen r).value <;> simp only [hl,hr] at h
    · contradiction
    · cases h;exact ir _ words.2 hr
    · cases h;exact il _ words.1 hl
    · simp only [copyBits_value,Option.some.injEq] at h
      subst out
      exact ⟨il _ words.1 hl,ir _ words.2 hr⟩

theorem eraseBits_work_nodes (W N : Nat) (chosen : List Bool) (t : BitTree)
 (words : TreeWords W t) (size : footprint (viewTree t)≤N) (cn : chosen.length≤N) :
 (eraseBits chosen t).work≤256*(W+4)*(N+1)*bitNodes t := by
 let K:=(W+4)*(N+1)
 have one:1≤K:=by simpa only [Nat.one_mul] using Nat.mul_le_mul (show 1≤W+4 by omega) (show 1≤N+1 by omega)
 have nk:N+1≤K:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (N+1) (show 1≤W+4 by omega)
 have aux (t : BitTree) (words : TreeWords W t) (size : footprint (viewTree t)≤N) :
  (eraseBits chosen t).work≤256*K*bitNodes t:=by
  induction t with
  | leaf g=>
   have gn:g.origin.length≤N:=by simp only [viewTree,viewGroup,footprint] at size;omega
   have e:(ownedAddressEqual g.origin chosen).work≤48*K:=Nat.le_trans (ownedAddressEqual_work N _ _ gn cn) (Nat.mul_le_mul_left 48 nk)
   have c:=copied_group_fee W N g ⟨words.1,words.2,size⟩
   have ck:(copyGroup g).work+4≤64*K:=by simpa only [K,groupFee,Nat.mul_assoc] using c
   simp only [eraseBits,bitNodes,Nat.mul_one]
   split <;> simp only [Charged.work] <;> omega
  | node p l r il ir=>
   have ls:footprint (viewTree l)≤N:=by simp only [viewTree,footprint] at size;omega
   have rs:footprint (viewTree r)≤N:=by simp only [viewTree,footprint] at size;omega
   have pn:p.length≤N:=by simp only [viewTree,footprint] at size;omega
   have a:=il words.1 ls;have b:=ir words.2 rs
   have e:(ownedAddressEqual p chosen).work≤48*K:=Nat.le_trans (ownedAddressEqual_work N _ _ pn cn) (Nat.mul_le_mul_left 48 nk)
   have path:(copyBits p).work≤8*K:=by rw [copyBits_work];omega
   have expand (A l r : Nat) : A*(1+l+r)=A*l+A*r+A:=by simp only [Nat.mul_add,Nat.mul_one];omega
   simp only [eraseBits,bitNodes,expand]
   split
   · simp only [Charged.work];omega
   · cases ha:(eraseBits chosen l).value <;> cases hb:(eraseBits chosen r).value <;>
      simp only [ha,hb,Charged.work] <;> omega
 simpa only [K,Nat.mul_assoc] using aux t words size

theorem eraseBits_source_bound (W N : Nat) (chosen : List Bool) (t : BitTree)
 (words : TreeWords W t) (size : footprint (viewTree t)≤N) (cn : chosen.length≤N) :
 (eraseBits chosen t).value.map viewTree=CoreProgram.erase chosen (viewTree t) ∧
 (eraseBits chosen t).work≤256*(W+4)*(N+1)*N ∧
 (∀out,(eraseBits chosen t).value=some out→TreeWords W out ∧ treeCells out≤(W+4)*N) := by
 have work:=Nat.le_trans (eraseBits_work_nodes W N chosen t words size cn)
  (Nat.mul_le_mul_left (256*(W+4)*(N+1)) (Nat.le_trans (bitNodes_footprint t) size))
 refine ⟨eraseBits_value chosen t,work,?_⟩
 intro out h
 have ow:=eraseBits_words W chosen t out words h
 have val:=eraseBits_value chosen t
 rw [h] at val
 have src:CoreProgram.erase chosen (viewTree t)=some (viewTree out):=val.symm
 have fp:=Nat.le_trans (erase_footprint chosen (viewTree t) (viewTree out) src) size
 exact ⟨ow,Nat.le_trans (treeCells_source_bound W out ow) (Nat.mul_le_mul_left (W+4) fp)⟩
end OrdinaryDispatch.RecoveryControlBits
