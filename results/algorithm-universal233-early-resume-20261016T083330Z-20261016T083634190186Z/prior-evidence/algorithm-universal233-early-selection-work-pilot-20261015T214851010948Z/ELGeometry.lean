import ELPrimitives
namespace OrdinaryDispatch.EarlyLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence

def meterVertices : Tree→Charged (List RMAF.Vertex)
 | .leaf _=>⟨[[]],4⟩
 | .node l r=>let a:=meterVertices l;let b:=meterVertices r
   ⟨[]::(a.value.map (false::·)++b.value.map (true::·)),a.work+b.work+8*(a.value.length+b.value.length+1)⟩
@[simp] theorem meterVertices_value (T : Tree) : (meterVertices T).value=HardParent.vertices T := by
 induction T <;> simp_all [meterVertices,HardParent.vertices,prependSide]
theorem vertices_depthone (T : Tree) : HardParent.vertices T=DepthOne.vertices T := by
 induction T <;> simp_all [HardParent.vertices,DepthOne.vertices,prependSide]
theorem vertices_length (T : Tree) : (HardParent.vertices T).length=treeNodes T := by
 induction T <;> simp_all [HardParent.vertices,prependSide,treeNodes];omega
theorem vertices_address (T : Tree) (v : RMAF.Vertex) (hv : v∈HardParent.vertices T) : v.length≤treeNodes T := by
 induction T generalizing v with
 | leaf x=>simp [HardParent.vertices] at hv;subst v;simp [treeNodes]
 | node l r il ir=>
  simp only [HardParent.vertices,prependSide,List.mem_cons,List.mem_append,List.mem_map] at hv
  rcases hv with rfl|⟨u,hu,rfl⟩|⟨u,hu,rfl⟩
  · simp [treeNodes]
  · have h:=il u hu;simp only [List.length_cons,treeNodes];omega
  · have h:=ir u hu;simp only [List.length_cons,treeNodes];omega

theorem meterVertices_bound (T : Tree) (N : Nat) (tn : treeNodes T≤N) :
 (meterVertices T).work≤8*(N+1)*treeNodes T := by
 induction T with
 | leaf x=>simp only [meterVertices,treeNodes,Nat.mul_one];omega
 | node l r il ir=>
  have ln : treeNodes l≤N:=by simp only [treeNodes] at tn;omega
  have rn : treeNodes r≤N:=by simp only [treeNodes] at tn;omega
  have a:=il ln;have b:=ir rn
  simp only [meterVertices,meterVertices_value,vertices_length,treeNodes,Nat.mul_add,Nat.mul_one] at a b tn ⊢;omega

def meterEdges (T : Tree) : Charged (List RMAF.Vertex) :=
 let v:=meterVertices T;⟨v.value.tail,v.work+4⟩
@[simp] theorem meterEdges_value (T : Tree) : (meterEdges T).value=DepthOne.edges T := by
 cases T <;> simp [meterEdges,meterVertices_value,vertices_depthone,DepthOne.vertices,DepthOne.edges]
theorem edges_length (T : Tree) : (DepthOne.edges T).length=treeNodes T-1 := by
 have h:=(vertices_length T)
 cases T <;> simp_all [HardParent.vertices,prependSide,DepthOne.edges,vertices_depthone,treeNodes];omega

def meterSubtree : Tree→RMAF.Vertex→Charged (Option Tree)
 | T,[]=>⟨some T,2⟩
 | .leaf _,_::_=>⟨none,2⟩
 | .node l r,s::v=>let a:=meterSubtree (if s then r else l) v;⟨a.value,a.work+4⟩
@[simp] theorem meterSubtree_value (T : Tree) (v : RMAF.Vertex) : (meterSubtree T v).value=CoreGraph.subtree T v := by
 induction v generalizing T with
 | nil=>rfl
 | cons s v ih=>cases T <;> simp [meterSubtree,CoreGraph.subtree,ih]
theorem meterSubtree_bound (T : Tree) (v : RMAF.Vertex) : (meterSubtree T v).work≤4*(v.length+1) := by
 induction v generalizing T with
 | nil=>simp [meterSubtree]
 | cons s v ih=>
  cases T with
  | leaf x=>simp [meterSubtree]
  | node l r=>have h:=ih (if s then r else l);simp only [meterSubtree,List.length_cons];omega

theorem subtree_nodes (T U : Tree) (v : RMAF.Vertex) (h : CoreGraph.subtree T v=some U) : treeNodes U≤treeNodes T := by
 induction v generalizing T with
 | nil=>simp [CoreGraph.subtree] at h;subst U;omega
 | cons s v ih=>
  cases T with
  | leaf x=>simp [CoreGraph.subtree] at h
  | node l r=>
   cases s
   · have a:=ih l (by simpa [CoreGraph.subtree] using h);simp only [treeNodes];omega
   · have a:=ih r (by simpa [CoreGraph.subtree] using h);simp only [treeNodes];omega

def meterSubtreeLabels (T : Tree) (v : RMAF.Vertex) : Charged (List Nat) :=
 let a:=meterSubtree T v
 match a.value with
 | none=>⟨[],a.work+2⟩
 | some U=>let b:=meterLeaves U;⟨b.value,a.work+b.work+2⟩
@[simp] theorem meterSubtreeLabels_value (T : Tree) (v : RMAF.Vertex) :
 (meterSubtreeLabels T v).value=DepthOne.subtreeLabels T v := by
 cases h : CoreGraph.subtree T v <;> simp [meterSubtreeLabels,DepthOne.subtreeLabels,h]
theorem hpLabels_eq (T : Tree) (v : RMAF.Vertex) : HardParent.subtreeLabels T v=DepthOne.subtreeLabels T v := by
 induction v generalizing T with
 | nil=>rfl
 | cons s v ih=>cases T with
  | leaf x=>rfl
  | node l r=>cases s <;> simpa [HardParent.subtreeLabels,DepthOne.subtreeLabels,CoreGraph.subtree] using ih _

theorem subtreeLabels_length (T : Tree) (v : RMAF.Vertex) : (DepthOne.subtreeLabels T v).length≤treeNodes T := by
 cases h : CoreGraph.subtree T v with
 | none=>simp [DepthOne.subtreeLabels,h]
 | some U=>simpa [DepthOne.subtreeLabels,h] using Nat.le_trans (leaves_nodes U) (subtree_nodes T U v h)

theorem meterSubtreeLabels_bound (T : Tree) (v : RMAF.Vertex) (N : Nat) (tn : treeNodes T≤N) (vn : v.length≤N) :
 (meterSubtreeLabels T v).work≤16*(N+1)^2 := by
 have a:=meterSubtree_bound T v
 cases h : (meterSubtree T v).value with
 | none=>simp only [meterSubtreeLabels,h];simp only [Nat.pow_two,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul];omega
 | some U=>
  have un:=Nat.le_trans (subtree_nodes T U v (by simpa using h)) tn
  have b:=meterLeaves_cap U N un
  have pos : N+1≤(N+1)^2:=by simpa using pow_mono N 1 2 (by decide)
  simp only [meterSubtreeLabels,h];omega

def meterDropLast : RMAF.Vertex→Charged RMAF.Vertex
 | []=>⟨[],1⟩ | [_]=>⟨[],2⟩
 | x::y::xs=>let r:=meterDropLast (y::xs);⟨x::r.value,r.work+4⟩
@[simp] theorem meterDropLast_value (v : RMAF.Vertex) : (meterDropLast v).value=v.dropLast := by
 induction v with
 | nil=>rfl
 | cons x xs ih=>cases xs <;> simp_all [meterDropLast,List.dropLast]
theorem meterDropLast_bound (v : RMAF.Vertex) : (meterDropLast v).work≤4*(v.length+1) := by
 induction v with
 | nil=>simp [meterDropLast]
 | cons x xs ih=>cases xs <;> simp_all only [meterDropLast,List.length_cons,List.length_nil] <;> omega

theorem minimal_two_bound (S : Tree) (a b N : Nat) (sn : treeNodes S≤N) :
 (meterMinimal [a,b] S).work≤80*(N+1)^3 := by
 have h:=meterMinimal_bound [a,b] S N sn
 have coef : 16*([a,b].length+N+2)+16≤80*(N+1) := by simp;omega
 have base : spanCap [a,b] N≤80*(N+1)^2 := by
  simpa only [spanCap,Nat.pow_two,Nat.mul_assoc] using Nat.mul_le_mul_right (N+1) coef
 have scale:=Nat.mul_le_mul base (Nat.le_trans sn (Nat.le_succ N))
 exact Nat.le_trans h (by simpa only [Nat.pow_succ,Nat.mul_assoc] using scale)

def meterPendantCheck (S : Tree) (a b : Nat) (v : RMAF.Vertex) : Charged Bool :=
 let d:=meterDropLast v
 let m:=meterMinimal [a,b] S;let c:=meterVertexContains d.value m.value
 let n:=meterMinimal [a,b] S;let e:=meterVertexContains v n.value
 ⟨!v.isEmpty&&c.value&&(!e.value),d.work+m.work+c.work+n.work+e.work+4⟩
@[simp] theorem meterPendantCheck_value (S a b v) :
 (meterPendantCheck S a b v).value=(!v.isEmpty&&(minimalVertices [a,b] S).contains v.dropLast&&(!(minimalVertices [a,b] S).contains v)) := by
 simp [meterPendantCheck]

theorem meterPendantCheck_bound (S : Tree) (a b N : Nat) (v : RMAF.Vertex)
 (sn : treeNodes S≤N) (vn : v.length≤N) : (meterPendantCheck S a b v).work≤256*(N+1)^3 := by
 have d:=meterDropLast_bound v
 have m:=minimal_two_bound S a b N sn
 have ml:=Nat.le_trans (minimal_length [a,b] S) sn
 have dv : v.dropLast.length≤N:=by simp only [List.length_dropLast];omega
 have cb:=meterVertexContains_bound v.dropLast (minimalVertices [a,b] S) N dv
 have eb:=meterVertexContains_bound v (minimalVertices [a,b] S) N vn
 have k:=Nat.mul_le_mul_left (8*(N+1)) (Nat.add_le_add_right ml 1)
 have c:=Nat.le_trans cb k;have e:=Nat.le_trans eb k
 have p1:=pow_mono N 1 3 (by decide);have p2:=pow_mono N 2 3 (by decide)
 have pos : 1≤(N+1)^3:=Nat.one_le_pow _ _ (by omega)
 simp only [Nat.pow_one,Nat.pow_two,Nat.mul_assoc] at c e p1 p2
 simp only [meterPendantCheck,meterDropLast_value,meterMinimal_value];omega

def meterPendant (S : Tree) (a b : Nat) : Charged (List RMAF.Vertex) :=
 let v:=meterVertices S;let f:=meterFilter (meterPendantCheck S a b) v.value
 ⟨f.value,v.work+f.work+2⟩
@[simp] theorem meterPendant_value (S a b) : (meterPendant S a b).value=HardParent.pendantOriginal S a b := by
 simp [meterPendant,HardParent.pendantOriginal]
theorem meterPendant_bound (S : Tree) (a b N : Nat) (sn : treeNodes S≤N) :
 (meterPendant S a b).work≤512*(N+1)^4 := by
 have v0:=meterVertices_bound S N sn
 have v:=Nat.le_trans v0 (Nat.mul_le_mul_left (8*(N+1)) (Nat.le_trans sn (Nat.le_succ N)))
 have f:=meterFilter_bound (meterPendantCheck S a b) (HardParent.vertices S) (256*(N+1)^3)
  (fun x hx=>meterPendantCheck_bound S a b N x sn (Nat.le_trans (vertices_address S x hx) sn))
 have p : 1≤(N+1)^3:=Nat.one_le_pow _ _ (by omega)
 have coeff : 256*(N+1)^3+4≤260*(N+1)^3:=by omega
 have scale:=Nat.mul_le_mul coeff (Nat.add_le_add_right sn 1)
 simp only [vertices_length] at f
 have ff:=Nat.le_trans f scale
 have lift:=pow_mono N 2 4 (by decide)
 have pos : 1≤(N+1)^4:=Nat.one_le_pow _ _ (by omega)
 have eq : 260*(N+1)^3*(N+1)=260*(N+1)^4 := by rw [Nat.pow_succ];ac_rfl
 change (meterFilter (meterPendantCheck S a b) (HardParent.vertices S)).work≤260*(N+1)^3*(N+1) at ff
 rw [eq] at ff
 simp only [meterPendant,meterVertices_value]
 have vv : (meterVertices S).work≤8*(N+1)^4:=Nat.le_trans v (by simpa only [Nat.pow_two,Nat.mul_assoc] using Nat.mul_le_mul_left 8 lift)
 omega

end OrdinaryDispatch.EarlyLocalWork
