import ELRule4Primitives
namespace OrdinaryDispatch.EarlyLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence

theorem all_scaled {α : Type} (f : α→Charged Bool) (xs : List α) (N k p C : Nat)
 (len : xs.length+1≤C*(N+1)) (point : ∀x∈xs,(f x).work≤k*(N+1)^p) :
 (meterAll f xs).work≤((k+4)*C)*(N+1)^(p+1) := by
 have a:=meterAll_bound f xs (k*(N+1)^p) point
 have pos : 1≤(N+1)^p:=Nat.one_le_pow _ _ (by omega)
 have coeff : k*(N+1)^p+4≤(k+4)*(N+1)^p:=by simp only [Nat.add_mul];omega
 have b:=Nat.mul_le_mul coeff len
 exact Nat.le_trans a (by simpa only [Nat.pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using b)

def meterNoCommon (T S : Tree) : Charged Bool :=
 let t:=meterOrderedCherries T
 let a:=meterAll (fun ab=>let s:=meterOrderedCherries S;let m:=meterPairContains ab s.value
   ⟨!m.value,s.work+m.work+2⟩) t.value
 ⟨a.value,t.work+a.work+2⟩
@[simp] theorem meterNoCommon_value (T S) :
 (meterNoCommon T S).value=(Rule4.orderedCherries T).all (fun p=>!(Rule4.orderedCherries S).contains p) := by simp [meterNoCommon]

def meterNoOne (T S : Tree) : Charged Bool :=
 let t:=meterOrderedCherries T
 let a:=meterAll (fun ab=>let p:=meterPendant S ab.1 ab.2
   ⟨p.value.length!=1,p.work+4*(p.value.length+1)+2⟩) t.value
 ⟨a.value,t.work+a.work+2⟩
@[simp] theorem meterNoOne_value (T S) :
 (meterNoOne T S).value=(Rule4.orderedCherries T).all (fun p=>(HardParent.pendantOriginal S p.1 p.2).length!=1) := by simp [meterNoOne]

def meterRule4Priority (T S : Tree) : Charged Bool :=
 let p:=meterOrdinaryProper T S;let c:=meterNoCommon T S
 let a:=meterNoOne T S;let b:=meterNoOne S T
 ⟨p.value&&c.value&&a.value&&b.value,p.work+c.work+a.work+b.work+8⟩
@[simp] theorem meterRule4Priority_value (T S) : (meterRule4Priority T S).value=decide (Rule4.Priority T S) := by
 apply Bool.eq_iff_iff.2
 simp [meterRule4Priority,DepthOne.proper,Rule4.Priority,Bool.and_eq_true,and_assoc]

theorem meterNoCommon_bound (T S : Tree) (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterNoCommon T S).work≤256*(N+1)^3 := by
 have t:=cap_lift N 32 2 3 _ (meterOrderedCherries_bound T N tn) (by decide)
 have s:=meterOrderedCherries_bound S N sn
 have tl:=orderedCherries_length T;have sl:=orderedCherries_length S
 let f : Nat×Nat→Charged Bool:=fun ab=>let s:=meterOrderedCherries S;let m:=meterPairContains ab s.value
   ⟨!m.value,s.work+m.work+2⟩
 have point (ab : Nat×Nat) : (f ab).work≤64*(N+1)^2 := by
  have m:=meterPairContains_bound ab (Rule4.orderedCherries S)
  have pow : N+1≤(N+1)^2:=by simpa using pow_mono N 1 2 (by decide)
  have pos : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
  simp only [f,meterOrderedCherries_value];omega
 have a:=all_scaled f (Rule4.orderedCherries T) N 64 2 2 (by omega) (fun ab _=>point ab)
 have pos : 1≤(N+1)^3:=Nat.one_le_pow _ _ (by omega)
 simp only [meterNoCommon,meterOrderedCherries_value];change (meterOrderedCherries T).work+(meterAll f (Rule4.orderedCherries T)).work+2≤_;omega

theorem meterNoOne_bound (T S : Tree) (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterNoOne T S).work≤4096*(N+1)^5 := by
 have t:=cap_lift N 32 2 5 _ (meterOrderedCherries_bound T N tn) (by decide)
 have tl:=orderedCherries_length T
 let f : Nat×Nat→Charged Bool:=fun ab=>let p:=meterPendant S ab.1 ab.2
   ⟨p.value.length!=1,p.work+4*(p.value.length+1)+2⟩
 have point (ab : Nat×Nat) : (f ab).work≤1024*(N+1)^4 := by
  have p:=meterPendant_bound S ab.1 ab.2 N sn
  have pl:=pendant_length S ab.1 ab.2
  have pow : N+1≤(N+1)^4:=by simpa using pow_mono N 1 4 (by decide)
  have pos : 1≤(N+1)^4:=Nat.one_le_pow _ _ (by omega)
  simp only [f,meterPendant_value];omega
 have a:=all_scaled f (Rule4.orderedCherries T) N 1024 4 2 (by omega) (fun ab _=>point ab)
 have pos : 1≤(N+1)^5:=Nat.one_le_pow _ _ (by omega)
 simp only [meterNoOne,meterOrderedCherries_value];change (meterOrderedCherries T).work+(meterAll f (Rule4.orderedCherries T)).work+2≤_;omega

theorem meterRule4Priority_bound (T S : Tree) (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterRule4Priority T S).work≤16384*(N+1)^5 := by
 have p:=cap_lift N 128 2 5 _ (meterOrdinaryProper_bound T S N tn sn) (by decide)
 have c:=cap_lift N 256 3 5 _ (meterNoCommon_bound T S N tn sn) (by decide)
 have a:=meterNoOne_bound T S N tn sn;have b:=meterNoOne_bound S T N sn tn
 have pos : 1≤(N+1)^5:=Nat.one_le_pow _ _ (by omega)
 simp only [meterRule4Priority];omega

def meterLocalGuard (T S : Tree) (raw : Rule4.RawChoice) : Charged Bool :=
 let t:=meterOrderedCherries T;let ta:=meterPairContains (raw.a,raw.b) t.value
 let s:=meterOrderedCherries S;let sa:=meterPairContains (raw.a,raw.c) s.value
 let p:=meterPendant S raw.a raw.b;let perm:=meterVertexPerm p.value [raw.cHead,raw.xHead]
 let lab:=meterSubtreeLabels S raw.cHead;let equal:=meterNatListEq lab.value [raw.c]
 ⟨ta.value&&sa.value&&(raw.a!=raw.b)&&perm.value&&equal.value,
  t.work+ta.work+s.work+sa.work+p.work+perm.work+lab.work+equal.work+16⟩
@[simp] theorem meterLocalGuard_value (T S raw) : (meterLocalGuard T S raw).value=decide (Rule4.LocalGuard T S raw) := by
 apply Bool.eq_iff_iff.2
 simp [meterLocalGuard,Rule4.LocalGuard,hpLabels_eq,Bool.and_eq_true,and_assoc]

theorem pendant_address (S : Tree) (a b : Nat) (v : RMAF.Vertex) (hv : v∈HardParent.pendantOriginal S a b) : v.length≤treeNodes S :=
 vertices_address S v (List.mem_of_mem_filter hv)

theorem meterLocalGuard_bound (T S : Tree) (raw : Rule4.RawChoice) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) (head : raw.cHead.length≤N) :
 (meterLocalGuard T S raw).work≤2048*(N+1)^4 := by
 have t:=cap_lift N 32 2 4 _ (meterOrderedCherries_bound T N tn) (by decide)
 have s:=cap_lift N 32 2 4 _ (meterOrderedCherries_bound S N sn) (by decide)
 have tl:=orderedCherries_length T;have sl:=orderedCherries_length S
 have ta:=meterPairContains_bound (raw.a,raw.b) (Rule4.orderedCherries T)
 have sa:=meterPairContains_bound (raw.a,raw.c) (Rule4.orderedCherries S)
 have p:=meterPendant_bound S raw.a raw.b N sn
 have perm:=meterVertexPerm_bound (HardParent.pendantOriginal S raw.a raw.b) [raw.cHead,raw.xHead] N
   (fun x hx=>Nat.le_trans (pendant_address S raw.a raw.b x hx) sn)
 have pl:=pendant_length S raw.a raw.b
 have permb:=Nat.mul_le_mul_left (20*(N+1)*(2+1)) (show (HardParent.pendantOriginal S raw.a raw.b).length+1≤N+1 by omega)
 have perm' : (meterVertexPerm (HardParent.pendantOriginal S raw.a raw.b) [raw.cHead,raw.xHead]).work≤60*(N+1)^2:=
   Nat.le_trans perm (by simpa only [List.length_cons,List.length_nil,Nat.pow_two,Nat.mul_assoc] using permb)
 have lab:=meterSubtreeLabels_bound S raw.cHead N sn head
 have eq:=meterNatListEq_bound (DepthOne.subtreeLabels S raw.cHead) [raw.c]
 have ll:=subtreeLabels_length S raw.cHead
 have p1 : N+1≤(N+1)^4:=by simpa using pow_mono N 1 4 (by decide)
 have p2:=pow_mono N 2 4 (by decide)
 have pos : 1≤(N+1)^4:=Nat.one_le_pow _ _ (by omega)
 simp only [meterLocalGuard,meterOrderedCherries_value,meterPendant_value,meterSubtreeLabels_value]
 omega

end OrdinaryDispatch.EarlyLocalWork
