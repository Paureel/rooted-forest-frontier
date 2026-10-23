import PaidParsing
namespace Universal233.Rule5RemainingLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork Rule5PaidSelector

def leafAtMeter (T : Tree) (q : RMAF.Vertex) (a : Nat) : Measured Bool :=
 let s:=subtreeMeter T q
 match s.value with
 | none=>⟨false,s.work+2⟩
 | some U=>let e:=leafEqMeter U a;⟨e.value,s.work+e.work+2⟩

theorem leaf_at_value (T : Tree) (q : RMAF.Vertex) (a : Nat) :
 (leafAtMeter T q a).value=decide (LeafAt T q a) := by
 apply Bool.eq_iff_iff.2
 simp only [leafAtMeter,subtree_value,decide_eq_true_eq,LeafAt]
 split <;> simp_all [leafEqMeter]

theorem leaf_at_work (T : Tree) (q : RMAF.Vertex) (a : Nat) :
 (leafAtMeter T q a).work≤2*q.length+6 := by
 have s:=subtree_work T q
 simp only [leafAtMeter];split <;> dsimp only [leafEqMeter] <;> omega

def findLeafMeter (T : Tree) (a : Nat) : List RMAF.Vertex→Measured (Option RMAF.Vertex)
 | []=>⟨none,1⟩
 | q::qs=>let h:=leafAtMeter T q a
           if h.value then ⟨some q,h.work+2⟩ else
            let r:=findLeafMeter T a qs;⟨r.value,h.work+r.work+2⟩

theorem find_leaf_value (T : Tree) (a : Nat) (qs : List RMAF.Vertex) :
 (findLeafMeter T a qs).value=qs.find? (fun q=>decide (LeafAt T q a)) := by
 induction qs with
 | nil=>rfl
 | cons q qs ih=>simp only [findLeafMeter,List.find?_cons,leaf_at_value];split <;> simp_all

theorem find_leaf_work (T : Tree) (a : Nat) (qs : List RMAF.Vertex) (N : Nat)
 (addr : ∀q,q∈qs→q.length≤N) : (findLeafMeter T a qs).work≤(2*N+8)*qs.length+1 := by
 induction qs with
 | nil=>simp [findLeafMeter]
 | cons q qs ih=>
  have h:=leaf_at_work T q a;have qn:=addr q (by simp)
  have r:=ih (fun u hu=>addr u (by simp [hu]))
  simp only [findLeafMeter,List.length_cons,Nat.mul_succ]
  split <;> dsimp only <;> omega

def leafAddressMeter (T : Tree) (a : Nat) : Measured (Option RMAF.Vertex) :=
 let vs:=verticesMeter T;let r:=findLeafMeter T a vs.value
 ⟨r.value,vs.work+r.work+1⟩

theorem leaf_address_value (T : Tree) (a : Nat) :
 (leafAddressMeter T a).value=leafAddress? T a := by
 simp only [leafAddressMeter,find_leaf_value,vertices_value,leafAddress?]

def leafAddressBudget (n : Nat) :=64*n*n+(2*n+8)*(2*n)+2

theorem leaf_address_work (T : Tree) (a : Nat) :
 (leafAddressMeter T a).work≤leafAddressBudget (leaves T).length := by
 have v:=vertices_work T;have vc:=vertices_count T
 have f:=find_leaf_work T a (verticesMeter T).value (leaves T).length
  (by intro q hq;have:=vertices_address T hq;omega)
 have scaled:=Nat.mul_le_mul_left (2*(leaves T).length+8)
  (show (verticesMeter T).value.length≤2*(leaves T).length by rw [vertices_value];omega)
 simp only [leafAddressMeter,leafAddressBudget];omega

theorem leaf_address_payload (T : Tree) (a : Nat) {q : RMAF.Vertex}
 (h : (leafAddressMeter T a).value=some q) :
 q∈vertices T ∧ q.length+1≤(leaves T).length ∧ LeafAt T q a := by
 rw [leaf_address_value] at h
 have mem : q∈vertices T := by
  have aux (qs : List RMAF.Vertex) : qs.find? (fun q=>decide (LeafAt T q a))=some q→q∈qs := by
   induction qs with
   | nil=>simp
   | cons p ps ih=>
     simp only [List.find?_cons]
     split
     · intro h;cases Option.some.inj h;simp
     · intro h;exact List.mem_cons_of_mem p (ih h)
  exact aux _ h
 refine ⟨mem,vertices_address T (by rw [vertices_value];exact mem),?_⟩
 exact of_decide_eq_true (List.find?_some (p:=fun p=>decide (LeafAt T p a)) h)
end Universal233.Rule5RemainingLocalWork
