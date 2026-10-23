import ELGeometry
namespace OrdinaryDispatch.EarlyLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence

def meterAgreement (T S : Tree) (F : List (List Nat)) : Charged Bool :=
 let t:=meterLeaves T;let pt:=meterPartition t.value F
 let s:=meterLeaves S;let ps:=meterPartition s.value F
 let shapes:=meterAll (meterRestrictionAgrees T S) F
 let et:=meterPairwise T F;let es:=meterPairwise S F
 ⟨pt.value&&ps.value&&shapes.value&&et.value&&es.value,
  t.work+pt.work+s.work+ps.work+shapes.work+et.work+es.work+8⟩
@[simp] theorem meterAgreement_value (T S F) : (meterAgreement T S F).value=agreement T S F := by
 simp [meterAgreement,agreement]
theorem meterAgreement_bound (T S : Tree) (F : List (List Nat)) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) (fl : F.length≤N) (cells : F.flatten.length≤N) :
 (meterAgreement T S F).work≤1024*(N+1)^5 := by
 have tl:=Nat.le_trans (leaves_nodes T) tn;have sl:=Nat.le_trans (leaves_nodes S) sn
 have a:=cap_lift N 8 2 5 _ (meterLeaves_cap T N tn) (by decide)
 have b:=cap_lift N 8 2 5 _ (meterLeaves_cap S N sn) (by decide)
 have pt:=cap_lift N 128 2 5 _ (meterPartition_bound (leaves T) F N tl fl cells) (by decide)
 have ps:=cap_lift N 128 2 5 _ (meterPartition_bound (leaves S) F N sl fl cells) (by decide)
 have sh0:=cap_all (meterRestrictionAgrees T S) F N 128 2 fl (fun B hb=>
  meterRestrictionAgrees_bound T S B N (by omega) (by omega) (Nat.le_trans (block_cells F B hb) cells))
 have sh:=cap_lift N 132 3 5 _ sh0 (by decide)
 have et:=meterPairwise_polynomial T F N tn tl fl (fun B hb=>Nat.le_trans (block_cells F B hb) cells)
 have es:=meterPairwise_polynomial S F N sn sl fl (fun B hb=>Nat.le_trans (block_cells F B hb) cells)
 have pos : 1≤(N+1)^5:=Nat.one_le_pow _ _ (by omega)
 simp only [meterAgreement,meterLeaves_value];omega

def meterComplement (S : Tree) (v : RMAF.Vertex) : Charged (List Nat) :=
 let leaves:=meterLeaves S
 let f:=meterFilter (fun x=>let a:=meterSubtreeLabels S v;let b:=meterContains x a.value
  ⟨!b.value,a.work+b.work+2⟩) leaves.value
 ⟨f.value,leaves.work+f.work+2⟩
@[simp] theorem meterComplement_value (S v) : (meterComplement S v).value=DepthOne.complement S v := by
 simp [meterComplement,DepthOne.complement]

def meterForest (S : Tree) : Option RMAF.Vertex→Charged (List (List Nat))
 | none=>let a:=meterLeaves S;⟨[a.value],a.work+2⟩
 | some v=>let a:=meterSubtreeLabels S v;let b:=meterComplement S v;⟨[a.value,b.value],a.work+b.work+4⟩
@[simp] theorem meterForest_value (S c) : (meterForest S c).value=DepthOne.forest S c := by
 cases c <;> simp [meterForest,DepthOne.forest]

theorem forest_cells (S : Tree) (c : Option RMAF.Vertex) :
 (DepthOne.forest S c).length≤2 ∧ (DepthOne.forest S c).flatten.length≤2*treeNodes S := by
 have leaves:=leaves_nodes S
 cases c with
 | none=>simp only [DepthOne.forest,List.length_cons,List.length_nil,List.flatten_cons,List.flatten_nil,List.append_nil];omega
 | some v=>
  have sub:=subtreeLabels_length S v
  have comp : (DepthOne.complement S v).length≤treeNodes S:=Nat.le_trans (List.length_filter_le _ _) leaves
  simp only [DepthOne.forest,List.length_cons,List.length_nil,List.flatten_cons,List.flatten_nil,List.length_append];omega

theorem meterForest_bound (S : Tree) (c : Option RMAF.Vertex) (N : Nat) (sn : treeNodes S≤N)
 (address : ∀v,c=some v → v.length≤N) : (meterForest S c).work≤128*(N+1)^3 := by
 have leaveswork:=meterLeaves_cap S N sn
 have leaflen:=Nat.le_trans (leaves_nodes S) sn
 have lift:=pow_mono N 2 3 (by decide)
 have pos : 1≤(N+1)^3:=Nat.one_le_pow _ _ (by omega)
 cases c with
 | none=>simp only [meterForest];omega
 | some v=>
  have vn:=address v rfl
  have sub:=meterSubtreeLabels_bound S v N sn vn
  have sublen:=Nat.le_trans (subtreeLabels_length S v) sn
  let f : Nat→Charged Bool:=fun x=>let a:=meterSubtreeLabels S v;let b:=meterContains x a.value
    ⟨!b.value,a.work+b.work+2⟩
  have point (x : Nat) : (f x).work≤32*(N+1)^2 := by
   have b:=meterContains_bound x (DepthOne.subtreeLabels S v)
   have b' : (meterContains x (DepthOne.subtreeLabels S v)).work≤4*(N+1):=
    Nat.le_trans b (Nat.mul_le_mul_left 4 (Nat.add_le_add_right sublen 1))
   have pow : N+1≤(N+1)^2:=by simpa using pow_mono N 1 2 (by decide)
   have p : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
   simp only [f,meterSubtreeLabels_value];omega
  have filt:=meterFilter_bound f (leaves S) (32*(N+1)^2) (fun x _=>point x)
  have pp : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
  have coeff : 32*(N+1)^2+4≤36*(N+1)^2:=by omega
  have prod:=Nat.mul_le_mul coeff (Nat.add_le_add_right leaflen 1)
  have ff : (meterFilter f (leaves S)).work≤36*(N+1)^3:=
   Nat.le_trans filt (by simpa only [show 3=2+1 from rfl,Nat.pow_succ,Nat.mul_assoc] using prod)
  simp only [meterForest,meterComplement,meterLeaves_value]
  change _≤128*(N+1)^3
  change (meterSubtreeLabels S v).work+((meterLeaves S).work+(meterFilter f (leaves S)).work+2)+4≤_
  omega

structure BestMeasured (α : Type) where
 value : Option α
 work : Nat
 checks : List (α×Bool)
 tailSizes : List Nat
 comparisons : List (Nat×Nat)
 deriving Repr

/-- Literal best inspects the complete tail even after an early valid candidate. -/
def meterBest {α : Type} (cost : α→Nat) (valid : α→Charged Bool) : List α→BestMeasured α
 | []=>⟨none,1,[],[],[]⟩
 | x::xs=>
  let a:=valid x;let r:=meterBest cost valid xs
  if a.value then
   match r.value with
   | none=>⟨some x,a.work+r.work+6,(x,true)::r.checks,xs.length::r.tailSizes,r.comparisons⟩
   | some y=>⟨if cost x≤cost y then some x else some y,a.work+r.work+10,
     (x,true)::r.checks,xs.length::r.tailSizes,(cost x,cost y)::r.comparisons⟩
  else ⟨r.value,a.work+r.work+4,(x,false)::r.checks,xs.length::r.tailSizes,r.comparisons⟩

@[simp] theorem meterBest_value {α : Type} (cost : α→Nat) (valid : α→Charged Bool) (xs : List α) :
 (meterBest cost valid xs).value=best cost (fun x=>(valid x).value) xs := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>
  by_cases h : (valid x).value=true
  · simp only [meterBest,best,h,if_true]
    rw [←ih]
    cases tail : (meterBest cost valid xs).value <;> simp
  · simp [meterBest,best,h,ih]

theorem meterBest_trace {α : Type} (cost : α→Nat) (valid : α→Charged Bool) (xs : List α) :
 (meterBest cost valid xs).checks=xs.map (fun x=>(x,(valid x).value)) ∧
 (meterBest cost valid xs).tailSizes=(List.range xs.length).reverse := by
 induction xs with
 | nil=>simp [meterBest]
 | cons x xs ih=>
  simp only [meterBest,List.map_cons,List.length_cons,List.range_succ,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.append_nil]
  by_cases h : (valid x).value=true
  · simp only [h,if_true]
    cases tail : (meterBest cost valid xs).value <;> simp [tail,ih.1,ih.2,h]
  · have hf : (valid x).value=false:=Bool.eq_false_iff.2 h
    simp [h,hf,ih.1,ih.2]

theorem meterBest_bound {α : Type} (cost : α→Nat) (valid : α→Charged Bool) (xs : List α) (A : Nat)
 (point : ∀x∈xs,(valid x).work≤A) : (meterBest cost valid xs).work≤(A+10)*(xs.length+1) := by
 induction xs with
 | nil=>simp [meterBest]
 | cons x xs ih=>
  have a:=point x (by simp);have b:=ih (fun y hy=>point y (by simp [hy]))
  simp only [Nat.mul_add,Nat.mul_one] at b
  simp only [meterBest,List.length_cons,Nat.mul_add,Nat.mul_one]
  split
  · cases tail : (meterBest cost valid xs).value <;> simp only [Charged.work] <;> omega
  · simp only [Charged.work];omega

def meterCandidates (S : Tree) : Charged (List (Option RMAF.Vertex)) :=
 let e:=meterEdges S
 ⟨none::e.value.map some,e.work+4*(e.value.length+1)⟩
@[simp] theorem meterCandidates_value (S) : (meterCandidates S).value=DepthOne.candidates S := by
 simp [meterCandidates,DepthOne.candidates]
theorem candidates_length (S : Tree) : (DepthOne.candidates S).length=treeNodes S := by
 have pos:=treeNodes_pos S
 simp only [DepthOne.candidates,List.length_cons,List.length_map,edges_length];omega

def meterCandidate (T S : Tree) (c : Option RMAF.Vertex) : Charged Bool :=
 let f:=meterForest S c;let a:=meterAgreement T S f.value
 ⟨a.value,f.work+a.work+2⟩
@[simp] theorem meterCandidate_value (T S c) : (meterCandidate T S c).value=agreement T S (DepthOne.forest S c) := by
 simp [meterCandidate]

def meterPretest (T S : Tree) : Charged DepthOne.Result :=
 let p:=meterOrdinaryProper T S
 if p.value then
  let c:=meterCandidates S;let b:=meterBest DepthOne.cutCost (meterCandidate T S) c.value
  ⟨match b.value with | none=>.rejected | some c=>.found c,p.work+c.work+b.work+4⟩
 else ⟨.refused,p.work+2⟩
@[simp] theorem meterPretest_value (T S) : (meterPretest T S).value=DepthOne.pretest01 T S := by
 simp only [meterPretest,DepthOne.pretest01,meterOrdinaryProper_value,meterCandidates_value,meterBest_value,meterCandidate_value]
 split <;> simp <;> rfl

end OrdinaryDispatch.EarlyLocalWork
