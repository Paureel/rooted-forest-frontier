import RINormalize
namespace OrdinaryDispatch.RecoveryInitialBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits

def bitNodes : BitTree→Nat
 | .leaf _=>1
 | .node _ l r=>1+bitNodes l+bitNodes r

theorem bitNodes_footprint (t : BitTree) : bitNodes t≤footprint (viewTree t) := by
 induction t with
 | leaf g=>simp only [bitNodes,viewTree,viewGroup,footprint];omega
 | node p l r il ir=>simp only [bitNodes,viewTree,footprint];omega

theorem normalizeBits_work_nodes (W N : Nat) (t : BitTree) (words : TreeWords W t)
 (size : footprint (viewTree t)≤N) :
 (normalizeBits t).work≤1024*(W+4)*(N+1)*bitNodes t := by
 let K:=(W+4)*(N+1)
 have one:1≤K:=by simpa only [Nat.one_mul] using Nat.mul_le_mul (show 1≤W+4 by omega) (show 1≤N+1 by omega)
 induction t with
 | leaf g=>
  have c:=copyGroup_work g
  have s:=treeCells_source_bound W (.leaf g) words
  have m:=Nat.mul_le_mul_left (W+4) (Nat.le_trans size (Nat.le_succ N))
  have d:=Nat.mul_le_mul_left 32 (Nat.le_trans s m)
  simp only [treeCells,Nat.mul_add,Nat.mul_one,Nat.succ_eq_add_one] at d
  simp only [normalizeBits,bitNodes,Nat.mul_one]
  calc _≤1024*K:=by omega
       _=1024*(W+4)*(N+1):=by simp only [K,Nat.mul_assoc]
 | node p l r il ir=>
  have ls:footprint (viewTree l)≤N:=by simp only [viewTree,footprint] at size;omega
  have rs:footprint (viewTree r)≤N:=by simp only [viewTree,footprint] at size;omega
  have path:p.length≤N:=by simp only [viewTree,footprint] at size;omega
  have a:=il words.1 ls;have b:=ir words.2 rs
  have nl:footprint (viewTree (normalizeBits l).value)≤N:=by
   rw [normalizeBits_value];exact Nat.le_trans (normalize_footprint _) ls
  have nr:footprint (viewTree (normalizeBits r).value)≤N:=by
   rw [normalizeBits_value];exact Nat.le_trans (normalize_footprint _) rs
  have c:=assemble_work W N p (normalizeBits l).value (normalizeBits r).value path
   (normalizeBits_words W l words.1) (normalizeBits_words W r words.2) nl nr
  have ck:(assemble p (normalizeBits l).value (normalizeBits r).value).work≤512*K:=by simpa only [K,Nat.mul_assoc] using c
  have expand (A l r : Nat) : A*(1+l+r)=A*l+A*r+A:=by simp only [Nat.mul_add,Nat.mul_one];omega
  simp only [normalizeBits,bitNodes,expand]
  have tail:1024*(W+4)*(N+1)=1024*K:=by simp only [K,Nat.mul_assoc]
  rw [tail] at *
  omega

/-- Actual represented normalizer including copied merges, color comparison,
closed discarded child trees, and copied original paths. -/
theorem normalizeBits_source_bound (W N : Nat) (t : BitTree) (words : TreeWords W t)
 (size : footprint (viewTree t)≤N) :
 viewTree (normalizeBits t).value=normalize (viewTree t) ∧
 (normalizeBits t).work≤1024*(W+4)*(N+1)*N ∧
 treeCells (normalizeBits t).value≤(W+4)*N := by
 have a:=normalizeBits_work_nodes W N t words size
 have n:=Nat.le_trans (bitNodes_footprint t) size
 have b:=Nat.mul_le_mul_left (1024*(W+4)*(N+1)) n
 have c:=treeCells_source_bound W (normalizeBits t).value (normalizeBits_words W t words)
 rw [normalizeBits_value] at c
 have d:=Nat.mul_le_mul_left (W+4) (Nat.le_trans (normalize_footprint (viewTree t)) size)
 exact ⟨normalizeBits_value t,by omega,by omega⟩
end OrdinaryDispatch.RecoveryInitialBits
