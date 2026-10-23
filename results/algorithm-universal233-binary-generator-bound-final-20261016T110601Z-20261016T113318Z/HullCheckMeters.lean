import TreeCheckMeters
namespace GenericForest.CheckCorrespondence
open RMAF ForestState Universal233 WholeSourceWork CoreWork

def meterDisjoint (A B : List RMAF.Vertex) : Charged Bool :=
 meterAll (fun v => let c:=meterVertexContains v B;⟨!c.value,c.work+1⟩) A
@[simp] theorem meterDisjoint_value (A B) : (meterDisjoint A B).value=disjointVertices A B := by
 simp [meterDisjoint,disjointVertices]

def meterHullPair (T : Tree) (B C : List Nat) : Charged Bool :=
 let a:=meterMinimal B T;let b:=meterMinimal C T;let d:=meterDisjoint a.value b.value
 ⟨d.value,a.work+b.work+d.work+2⟩
@[simp] theorem meterHullPair_value (T B C) :
 (meterHullPair T B C).value=disjointVertices (minimalVertices B T) (minimalVertices C T) := by
 simp [meterHullPair]

def meterPairwise (T : Tree) : Forest → Charged Bool
 | []=>⟨true,1⟩
 | B::F=>let a:=meterAll (meterHullPair T B) F;let r:=meterPairwise T F
         ⟨a.value&&r.value,a.work+r.work+4⟩
@[simp] theorem meterPairwise_value (T F) : (meterPairwise T F).value=pairwiseEmbeddings T F := by
 induction F with
 | nil=>rfl
 | cons B F ih=>simp [meterPairwise,pairwiseEmbeddings,ih]

theorem meterMinimal_polynomial (T : Tree) (B : List Nat) (N : Nat)
 (tn : treeNodes T≤N) (bl : B.length≤N) :
 (meterMinimal B T).work≤48*(N+1)^3 := by
 have h:=meterMinimal_bound B T N tn
 have cap : spanCap B N≤48*(N+1)^2 := by
  unfold spanCap
  have a : 16*(B.length+N+2)+16≤48*(N+1):=by omega
  have k:=Nat.mul_le_mul_right (N+1) a
  simpa only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] using k
 have k:=Nat.mul_le_mul cap (Nat.le_trans tn (Nat.le_succ N))
 exact Nat.le_trans h (by simpa only [Nat.pow_succ,Nat.mul_assoc] using k)

theorem meterDisjoint_polynomial (A B : List RMAF.Vertex) (N : Nat)
 (al : A.length≤N) (bl : B.length≤N) (address : ∀v∈A,v.length≤N) :
 (meterDisjoint A B).work≤13*(N+1)^3 := by
 have point (v) (hv : v∈A) :
  (let c:=meterVertexContains v B; (⟨!c.value,c.work+1⟩ : Charged Bool)).work≤9*(N+1)^2 := by
  have h:=meterVertexContains_bound v B N (address v hv)
  have k:=Nat.mul_le_mul_left (8*(N+1)) (Nat.add_le_add_right bl 1)
  have pos : 1≤(N+1)^2:=by exact Nat.one_le_pow _ _ (by omega)
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at h k pos ⊢
  omega
 have all:=meterAll_bound (fun v=>let c:=meterVertexContains v B;⟨!c.value,c.work+1⟩) A (9*(N+1)^2) point
 have pos : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
 have coefficient : 9*(N+1)^2+4≤13*(N+1)^2:=by omega
 have k:=Nat.mul_le_mul coefficient (Nat.add_le_add_right al 1)
 exact Nat.le_trans all (by simpa only [Nat.pow_succ,Nat.mul_assoc] using k)

theorem meterHullPair_polynomial (T : Tree) (B C : List Nat) (N : Nat)
 (tn : treeNodes T≤N) (tl : (leaves T).length≤N)
 (bl : B.length≤N) (cl : C.length≤N) :
 (meterHullPair T B C).work≤111*(N+1)^3 := by
 have a:=meterMinimal_polynomial T B N tn bl
 have b:=meterMinimal_polynomial T C N tn cl
 have d:=meterDisjoint_polynomial (minimalVertices B T) (minimalVertices C T) N
   (Nat.le_trans (minimal_length B T) tn) (Nat.le_trans (minimal_length C T) tn)
   (fun v hv=>by have h:=minimal_address B T v hv;omega)
 have pos : 1≤(N+1)^3:=Nat.one_le_pow _ _ (by omega)
 simp only [meterHullPair,meterMinimal_value];omega

theorem meterPairwise_bound (T : Tree) (F : Forest) (A : Nat)
 (point : ∀B∈F,∀C∈F,(meterHullPair T B C).work≤A) :
 (meterPairwise T F).work≤(A+9)*(F.length+1)^2 := by
 induction F with
 | nil=>simp [meterPairwise]
 | cons B F ih=>
  have tailBound:=ih (fun C hc D hd=>point C (by simp [hc]) D (by simp [hd]))
  have row:=meterAll_bound (meterHullPair T B) F A (fun C hc=>point B (by simp) C (by simp [hc]))
  have pos : 1≤(F.length+1)^2:=Nat.one_le_pow _ _ (by omega)
  simp only [meterPairwise,List.length_cons,Nat.pow_succ,Nat.pow_zero,Nat.mul_one,Nat.one_mul,
    Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at tailBound row pos ⊢
  omega

theorem meterPairwise_polynomial (T : Tree) (F : Forest) (N : Nat)
 (tn : treeNodes T≤N) (tl : (leaves T).length≤N) (fl : F.length≤N)
 (blocks : ∀B∈F,B.length≤N) :
 (meterPairwise T F).work≤120*(N+1)^5 := by
 have h:=meterPairwise_bound T F (111*(N+1)^3)
   (fun B hb C hc=>meterHullPair_polynomial T B C N tn tl (blocks B hb) (blocks C hc))
 have pos : 1≤(N+1)^3:=Nat.one_le_pow _ _ (by omega)
 have cap : 111*(N+1)^3+9≤120*(N+1)^3:=by omega
 have sq:=Nat.mul_self_le_mul_self (Nat.add_le_add_right fl 1)
 have k:=Nat.mul_le_mul cap sq
 have eq : 120*(N+1)^3*((N+1)*(N+1))=120*(N+1)^5:=by
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_assoc]
 exact Nat.le_trans h (by simpa only [Nat.pow_two,eq] using k)
end GenericForest.CheckCorrespondence
