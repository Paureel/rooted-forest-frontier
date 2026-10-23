import RIInterface
namespace OrdinaryDispatch.RecoveryInitialBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits

def closeGroup (g : BitGroup) : Charged Unit :=
 let a:=closeBits g.origin;let l:=closeArrays g.labels;let c:=closeBits g.color
 ⟨(),a.work+l.work+c.work+12⟩
theorem closeGroup_work (g : BitGroup) : (closeGroup g).work≤32*groupCells g := by
 have l:=closeArrays_work g.labels
 simp only [closeGroup,closeBits_work,groupCells,Nat.mul_add,Nat.mul_one] at *;omega

def closeTree : BitTree→Charged Unit
 | .leaf g=>let r:=closeGroup g;⟨(),r.work+4⟩
 | .node p l r=>let a:=closeBits p;let x:=closeTree l;let y:=closeTree r
   ⟨(),a.work+x.work+y.work+12⟩
theorem closeTree_work (t : BitTree) : (closeTree t).work≤64*treeCells t := by
 induction t with
 | leaf g=>have a:=closeGroup_work g;simp only [closeTree,treeCells,Nat.mul_add,Nat.mul_one];omega
 | node p l r il ir=>simp only [closeTree,closeBits_work,treeCells,Nat.mul_add,Nat.mul_one];omega

def mergeGroups (p : List Bool) (a b : BitGroup) : Charged BitTree :=
 let l:=copyArrays a.labels;let r:=copyArrays b.labels;let j:=appendRefs l.value r.value
 let spine:=closeSpine l.value;let color:=copyBits a.color;let path:=copyBits p
 ⟨.leaf ⟨path.value,j.value,color.value⟩,l.work+r.work+j.work+spine.work+color.work+path.work+12⟩
@[simp] theorem mergeGroups_value (p : List Bool) (a b : BitGroup) :
 (mergeGroups p a b).value=.leaf ⟨p,a.labels++b.labels,a.color⟩ := by simp [mergeGroups]

def assemble (p : List Bool) (l r : BitTree) : Charged BitTree :=
 match l,r with
 | .leaf a,.leaf b=>
  let e:=ownedEqual a.color b.color
  if e.value then
   let m:=mergeGroups p a b;let ca:=closeTree l;let cb:=closeTree r
   ⟨m.value,e.work+m.work+ca.work+cb.work+12⟩
  else let path:=copyBits p;⟨.node path.value l r,e.work+path.work+12⟩
 | _,_=>let path:=copyBits p;⟨.node path.value l r,path.work+12⟩

def normalizeBits : BitTree→Charged BitTree
 | .leaf g=>let c:=copyGroup g;⟨.leaf c.value,c.work+4⟩
 | .node p l r=>let a:=normalizeBits l;let b:=normalizeBits r;let c:=assemble p a.value b.value
   ⟨c.value,a.work+b.work+c.work+8⟩

@[simp] theorem normalizeBits_value (t : BitTree) : viewTree (normalizeBits t).value=normalize (viewTree t) := by
 induction t with
 | leaf g=>simp [normalizeBits,viewTree]
 | node p l r il ir=>
  cases hl:(normalizeBits l).value with
  | leaf a=>
   cases hr:(normalizeBits r).value with
   | leaf b=>
    simp only [hl,hr,viewTree] at il ir
    simp only [normalizeBits,assemble,hl,hr,ownedEqual_value]
    by_cases eq:decode a.color=decode b.color
    · simp [eq,viewTree,viewGroup,normalize,←il,←ir,List.map_append]
    · simp [eq,viewTree,viewGroup,normalize,←il,←ir]
   | node q a b=>simp [normalizeBits,assemble,hl,hr,viewTree,normalize,←il,←ir]
  | node q a b=>cases hr:(normalizeBits r).value <;> simp [normalizeBits,assemble,hl,hr,viewTree,normalize,←il,←ir]

theorem normalizeBits_words (W : Nat) (t : BitTree) (h : TreeWords W t) : TreeWords W (normalizeBits t).value := by
 induction t with
 | leaf g=>simpa [normalizeBits] using h
 | node p l r il ir=>
  have a:=il h.1;have b:=ir h.2
  cases hl:(normalizeBits l).value with
  | leaf x=>
   cases hr:(normalizeBits r).value with
   | leaf y=>
    simp only [hl,hr,TreeWords] at a b
    simp only [normalizeBits,assemble,hl,hr]
    split
    · simp only [mergeGroups_value,TreeWords,List.mem_append]
      exact ⟨by intro z hz;rcases hz with hz|hz;exact a.1 z hz;exact b.1 z hz,a.2⟩
    · simpa only [copyBits_value,TreeWords] using And.intro a b
   | node q x y=>simpa [normalizeBits,assemble,hl,hr,TreeWords] using And.intro a b
  | node q x y=>cases hr:(normalizeBits r).value <;> simpa [normalizeBits,assemble,hl,hr,TreeWords] using And.intro a b

theorem mergeGroups_work (W N : Nat) (p : List Bool) (a b : BitGroup)
 (pw : p.length≤N) (aw : ∀x∈a.labels,x.length≤W) (bw : ∀x∈b.labels,x.length≤W)
 (ac : a.color.length≤W) (al : a.labels.length≤N) (bl : b.labels.length≤N) :
 (mergeGroups p a b).work≤128*(W+4)*(N+1) := by
 have ca:=copyArrays_work a.labels;have cb:=copyArrays_work b.labels
 have la:=arrayCells_bound W a.labels aw;have lb:=arrayCells_bound W b.labels bw
 let K:=(W+4)*(N+1)
 have scale:(W+1)*N≤K:=Nat.mul_le_mul (by omega) (by omega)
 have sa:=Nat.mul_le_mul_left (W+1) al;have sb:=Nat.mul_le_mul_left (W+1) bl
 have kn:N≤K:=by have z:=Nat.mul_le_mul_right (N+1) (show 1≤W+4 by omega);simp only [Nat.one_mul] at z;omega
 have kw:W≤K:=by have z:=Nat.mul_le_mul_left (W+4) (show 1≤N+1 by omega);simp only [Nat.mul_one] at z;omega
 have kp:1≤K:=by omega
 simp only [mergeGroups,copyArrays_value,appendRefs_work,closeSpine_work,copyBits_work]
 calc _≤128*K:=by omega
      _=128*(W+4)*(N+1):=by simp only [K,Nat.mul_assoc]

theorem assemble_work (W N : Nat) (p : List Bool) (l r : BitTree)
 (pw : p.length≤N) (lw : TreeWords W l) (rw : TreeWords W r)
 (ls : footprint (viewTree l)≤N) (rs : footprint (viewTree r)≤N) :
 (assemble p l r).work≤512*(W+4)*(N+1) := by
 let K:=(W+4)*(N+1)
 have kn:N≤K:=by have z:=Nat.mul_le_mul_right (N+1) (show 1≤W+4 by omega);simp only [Nat.one_mul] at z;omega
 have kw:W+1≤K:=by have z:=Nat.mul_le_mul_left (W+4) (show 1≤N+1 by omega);simp only [Nat.mul_one] at z;omega
 have leftClose:(closeTree l).work≤64*K:=by
  have a:=closeTree_work l;have b:=treeCells_source_bound W l lw
  have c:=Nat.mul_le_mul_left (W+4) (Nat.le_trans ls (Nat.le_succ N))
  have d:=Nat.mul_le_mul_left 64 (Nat.le_trans b c)
  simp only [K,Nat.mul_assoc] at d ⊢;omega
 have rightClose:(closeTree r).work≤64*K:=by
  have a:=closeTree_work r;have b:=treeCells_source_bound W r rw
  have c:=Nat.mul_le_mul_left (W+4) (Nat.le_trans rs (Nat.le_succ N))
  have d:=Nat.mul_le_mul_left 64 (Nat.le_trans b c)
  simp only [K,Nat.mul_assoc] at d ⊢;omega
 cases l with
 | leaf a=>
  cases r with
  | leaf b=>
   have eq:=ownedEqual_work W a.color b.color lw.2 rw.2
   have al:a.labels.length≤N:=by simp only [viewTree,viewGroup,footprint,List.length_map] at ls;omega
   have bl:b.labels.length≤N:=by simp only [viewTree,viewGroup,footprint,List.length_map] at rs;omega
   have merge:=mergeGroups_work W N p a b pw lw.1 rw.1 lw.2 al bl
   have m:(mergeGroups p a b).work≤128*K:=by simpa only [K,Nat.mul_assoc] using merge
   simp only [assemble,copyBits_work]
   split <;> simp only [Charged.work] <;>
    (calc _≤512*K:=by omega
          _=512*(W+4)*(N+1):=by simp only [K,Nat.mul_assoc])
  | node q a b=>simp only [assemble,copyBits_work];calc _≤512*K:=by omega
                                                    _=512*(W+4)*(N+1):=by simp only [K,Nat.mul_assoc]
 | node q a b=>cases r <;> simp only [assemble,copyBits_work] <;>
   (calc _≤512*K:=by omega
         _=512*(W+4)*(N+1):=by simp only [K,Nat.mul_assoc])
end OrdinaryDispatch.RecoveryInitialBits
