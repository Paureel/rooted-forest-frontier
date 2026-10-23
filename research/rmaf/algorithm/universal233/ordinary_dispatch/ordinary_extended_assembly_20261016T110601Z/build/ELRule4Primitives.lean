import ELCherry
namespace OrdinaryDispatch.EarlyLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence

def meterPairContains (x : Nat×Nat) : List (Nat×Nat)→Charged Bool
 | []=>⟨false,1⟩
 | y::ys=>if x.1==y.1 && x.2==y.2 then ⟨true,8⟩ else let r:=meterPairContains x ys;⟨r.value,r.work+8⟩
@[simp] theorem meterPairContains_value (x : Nat×Nat) (ys : List (Nat×Nat)) :
 (meterPairContains x ys).value=ys.contains x := by
 induction ys with
 | nil=>rfl
 | cons y ys ih=>
  have eq : (x.1==y.1 && x.2==y.2)=(x==y):=rfl
  simp only [meterPairContains,eq,List.contains_cons]
  cases h:x==y <;> simp [h,ih]
theorem meterPairContains_bound (x : Nat×Nat) (ys : List (Nat×Nat)) :
 (meterPairContains x ys).work≤8*(ys.length+1) := by
 induction ys with
 | nil=>simp [meterPairContains]
 | cons y ys ih=>simp only [meterPairContains,List.length_cons,Nat.mul_add,Nat.mul_one];split <;> simp only [Charged.work] <;> omega

def meterOrderedCherries : Tree→Charged (List (Nat×Nat))
 | .leaf _=>⟨[],2⟩
 | .node l r=>let a:=meterOrderedCherries l;let b:=meterOrderedCherries r
  ⟨(match l,r with | .leaf x,.leaf y=>[(x,y),(y,x)] | _,_=>[])++a.value++b.value,
   a.work+b.work+8*(a.value.length+b.value.length+3)⟩
@[simp] theorem meterOrderedCherries_value (T : Tree) :
 (meterOrderedCherries T).value=Rule4.orderedCherries T := by
 induction T <;> simp_all [meterOrderedCherries,Rule4.orderedCherries] <;> rfl
theorem orderedCherries_length (T : Tree) : (Rule4.orderedCherries T).length≤2*treeNodes T := by
 induction T with
 | leaf x=>simp [Rule4.orderedCherries,treeNodes]
 | node l r il ir=>cases l <;> cases r <;> simp_all [Rule4.orderedCherries,treeNodes] <;> omega

theorem meterOrderedCherries_bound (T : Tree) (N : Nat) (tn : treeNodes T≤N) :
 (meterOrderedCherries T).work≤32*(N+1)^2 := by
 have h : (meterOrderedCherries T).work≤32*(N+1)*treeNodes T := by
  induction T with
  | leaf x=>simp only [meterOrderedCherries,treeNodes,Nat.mul_one];omega
  | node l r il ir=>
   have ln : treeNodes l≤N:=by simp only [treeNodes] at tn;omega
   have rn : treeNodes r≤N:=by simp only [treeNodes] at tn;omega
   have a:=il ln;have b:=ir rn;have al:=orderedCherries_length l;have bl:=orderedCherries_length r
   simp only [meterOrderedCherries,meterOrderedCherries_value,treeNodes,Nat.mul_add,Nat.mul_one] at tn a b ⊢;omega
 exact Nat.le_trans h (by simpa only [Nat.pow_two,Nat.mul_assoc] using Nat.mul_le_mul_left (32*(N+1)) (Nat.le_trans tn (Nat.le_succ N)))

def meterVertexErase (x : RMAF.Vertex) : List RMAF.Vertex→Charged (List RMAF.Vertex)
 | []=>⟨[],1⟩
 | y::ys=>let eq:=meterAddressEq x y
   if eq.value then ⟨ys,eq.work+4⟩ else let r:=meterVertexErase x ys;⟨y::r.value,eq.work+r.work+4⟩
@[simp] theorem meterVertexErase_value (x : RMAF.Vertex) (ys : List RMAF.Vertex) :
 (meterVertexErase x ys).value=ys.erase x := by
 induction ys with
 | nil=>rfl
 | cons y ys ih=>
  by_cases eq:x=y
  · subst y;simp [meterVertexErase]
  · have ne:=Ne.symm eq;simp [meterVertexErase,ih,eq,ne]
theorem meterVertexErase_bound (x : RMAF.Vertex) (ys : List RMAF.Vertex) (N : Nat) (xn : x.length≤N) :
 (meterVertexErase x ys).work≤8*(N+1)*(ys.length+1) := by
 induction ys with
 | nil=>simp only [meterVertexErase,List.length_nil,Nat.zero_add,Nat.mul_one];omega
 | cons y ys ih=>
  have eq:=meterAddressEq_bound x y
  have step : 4*(x.length+1)+4≤8*(N+1):=by omega
  simp only [meterVertexErase,List.length_cons,Nat.mul_add,Nat.mul_one] at *
  split <;> simp only [Charged.work] <;> omega

def meterVertexPerm : List RMAF.Vertex→List RMAF.Vertex→Charged Bool
 | [],ys=>⟨ys.isEmpty,1⟩
 | x::xs,ys=>let c:=meterVertexContains x ys;let e:=meterVertexErase x ys;let r:=meterVertexPerm xs e.value
   ⟨c.value&&r.value,c.work+e.work+r.work+4⟩
@[simp] theorem meterVertexPerm_value (xs ys : List RMAF.Vertex) :
 (meterVertexPerm xs ys).value=decide (xs.Perm ys) := by
 have val : ∀ys,(meterVertexPerm xs ys).value=xs.isPerm ys := by
  induction xs with
  | nil=>intro ys;rfl
  | cons x xs ih=>intro ys;simp [meterVertexPerm,List.isPerm,ih]
 rw [val];exact Bool.eq_iff_iff.2 (by simp only [List.isPerm_iff,decide_eq_true_eq])
theorem meterVertexPerm_bound (xs ys : List RMAF.Vertex) (N : Nat) (xn : ∀x∈xs,x.length≤N) :
 (meterVertexPerm xs ys).work≤20*(N+1)*(ys.length+1)*(xs.length+1) := by
 induction xs generalizing ys with
 | nil=>simp only [meterVertexPerm,List.length_nil,Nat.zero_add,Nat.mul_one,Nat.mul_assoc];have p:=Nat.mul_pos (show 0<N+1 by omega) (show 0<ys.length+1 by omega);omega
 | cons x xs ih=>
  have xx:=xn x (by simp)
  have a:=meterVertexContains_bound x ys N xx;have b:=meterVertexErase_bound x ys N xx
  have r:=ih ((meterVertexErase x ys).value) (fun y hy=>xn y (by simp [hy]))
  have el : (meterVertexErase x ys).value.length≤ys.length:=by simp only [meterVertexErase_value];exact List.length_erase_le
  have scale:=Nat.mul_le_mul_right (xs.length+1) (Nat.mul_le_mul_left (20*(N+1)) (Nat.add_le_add_right el 1))
  have rr:=Nat.le_trans r scale
  let B:=(N+1)*(ys.length+1)
  have positive : 1≤B:=Nat.mul_pos (by omega) (by omega)
  have aa : (meterVertexContains x ys).work≤8*B:=by simpa only [B,Nat.mul_assoc] using a
  have bb : (meterVertexErase x ys).work≤8*B:=by simpa only [B,Nat.mul_assoc] using b
  have rr' : (meterVertexPerm xs (meterVertexErase x ys).value).work≤20*B*(xs.length+1):=by simpa only [B,Nat.mul_assoc] using rr
  have step : (meterVertexContains x ys).work+(meterVertexErase x ys).work+4≤20*B:=by omega
  have goal : (meterVertexContains x ys).work+(meterVertexErase x ys).work+
    (meterVertexPerm xs (meterVertexErase x ys).value).work+4≤20*B*((xs.length+1)+1) := by
   rw [Nat.mul_succ]
   omega
  simpa only [meterVertexPerm,List.length_cons,B,Nat.mul_assoc] using goal


def meterNatListEq : List Nat→List Nat→Charged Bool
 | [],[]=>⟨true,2⟩ | [],_::_=>⟨false,2⟩ | _::_,[]=>⟨false,2⟩
 | x::xs,y::ys=>if x==y then let r:=meterNatListEq xs ys;⟨r.value,r.work+4⟩ else ⟨false,4⟩
@[simp] theorem meterNatListEq_value (xs ys : List Nat) : (meterNatListEq xs ys).value=(xs==ys) := by
 induction xs generalizing ys with
 | nil=>cases ys <;> rfl
 | cons x xs ih=>cases ys with
  | nil=>rfl
  | cons y ys=>cases h:x==y <;> simp [meterNatListEq,h,ih]
theorem meterNatListEq_bound (xs ys : List Nat) : (meterNatListEq xs ys).work≤4*(xs.length+1) := by
 induction xs generalizing ys with
 | nil=>cases ys <;> simp [meterNatListEq]
 | cons x xs ih=>cases ys with
  | nil=>simp only [meterNatListEq,List.length_cons];omega
  | cons y ys=>have r:=ih ys;simp only [meterNatListEq,List.length_cons,Nat.mul_add,Nat.mul_one];split <;> simp only [Charged.work] <;> omega

end OrdinaryDispatch.EarlyLocalWork
