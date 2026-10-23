import PendantCutWork
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork

def subtreeLabelsMeter : Tree→RMAF.Vertex→Measured (List Nat)
 | T,[]=>let l:=leavesMeter T;⟨l.value,l.work+1⟩
 | .leaf _,_::_=>⟨[],1⟩
 | .node l r,s::p=>let m:=subtreeLabelsMeter (if s then r else l) p;⟨m.value,m.work+2⟩

theorem subtree_labels_value (T : Tree) (p : RMAF.Vertex) :
 (subtreeLabelsMeter T p).value=subtreeLabels T p := by
 induction p generalizing T with
 | nil=>simp only [subtreeLabelsMeter,subtreeLabels,leaves_value]
 | cons s p ih=>cases T with
   | leaf x=>rfl
   | node l r=>simp only [subtreeLabelsMeter,subtreeLabels,ih]

theorem subtree_labels_work (T : Tree) (p : RMAF.Vertex) :
 (subtreeLabelsMeter T p).work≤4*(leaves T).length*(leaves T).length+2*p.length+2 := by
 induction p generalizing T with
 | nil=>have l:=leaves_work T;simp only [subtreeLabelsMeter,List.length_nil];omega
 | cons s p ih=>cases T with
   | leaf x=>simp [subtreeLabelsMeter,leaves]
   | node l r=>
     have hl:=ih l
     have hr:=ih r
     have nl : (leaves l).length≤(leaves (.node l r)).length := by simp only [leaves,List.length_append];omega
     have nr : (leaves r).length≤(leaves (.node l r)).length := by simp only [leaves,List.length_append];omega
     have ml:=Nat.mul_le_mul_left 4 (Nat.mul_le_mul nl nl)
     have mr:=Nat.mul_le_mul_left 4 (Nat.mul_le_mul nr nr)
     cases s <;> simp only [subtreeLabelsMeter,Bool.false_eq_true,ite_false,ite_true,List.length_cons]
     all_goals simp only [Nat.mul_assoc] at *
     all_goals omega

theorem subtree_labels_payload (T : Tree) (p : RMAF.Vertex) :
 (subtreeLabelsMeter T p).value.length≤(leaves T).length ∧
 (subtreeLabelsMeter T p).value⊆leaves T := by
 rw [subtree_labels_value]
 have sub:=subtreeLabels_sublist T p
 exact ⟨sub.length_le,sub.subset⟩

def blocksMeter (T : Tree) : List RMAF.Vertex→Measured (List (List Nat))
 | []=>⟨[],1⟩
 | p::ps=>let b:=subtreeLabelsMeter T p;let r:=blocksMeter T ps
           ⟨b.value::r.value,b.work+r.work+1⟩

theorem blocks_value (T : Tree) (ps : List RMAF.Vertex) :
 (blocksMeter T ps).value=ps.map (subtreeLabels T) := by
 induction ps with
 | nil=>rfl
 | cons p ps ih=>simp only [blocksMeter,List.map_cons,subtree_labels_value,ih]

theorem blocks_work (T : Tree) (ps : List RMAF.Vertex) (N : Nat)
 (addresses : ∀p,p∈ps →p.length≤N) :
 (blocksMeter T ps).work≤(4*(leaves T).length*(leaves T).length+2*N+3)*ps.length+1 := by
 induction ps with
 | nil=>simp [blocksMeter]
 | cons p ps ih=>
   have head:=subtree_labels_work T p
   have hp:=addresses p (by simp)
   have tail:=ih (fun q hq=>addresses q (by simp [hq]))
   simp only [blocksMeter,List.length_cons,Nat.mul_succ]
   omega

theorem blocks_payload (T : Tree) (ps : List RMAF.Vertex) :
 (blocksMeter T ps).value.length=ps.length ∧
 (blocksMeter T ps).value.flatten.length≤(leaves T).length*ps.length ∧
 (blocksMeter T ps).value.flatten⊆leaves T := by
 induction ps with
 | nil=>simp [blocksMeter]
 | cons p ps ih=>
   have block:=subtree_labels_payload T p
   refine ⟨by simp only [blocksMeter,List.length_cons,ih.1],?_,?_⟩
   · simp only [blocksMeter,List.flatten_cons,List.length_append,List.length_cons,Nat.mul_succ]
     omega
   · intro x hx
     simp only [blocksMeter,List.flatten_cons,List.mem_append] at hx
     rcases hx with hx|hx
     · exact block.2 hx
     · exact ih.2.2 hx

def flattenMeter : List (List Nat)→Measured (List Nat)
 | []=>⟨[],1⟩
 | B::bs=>let r:=flattenMeter bs;⟨B++r.value,r.work+B.length+1⟩

theorem flatten_value (bs : List (List Nat)) : (flattenMeter bs).value=bs.flatten := by
 induction bs with
 | nil=>rfl
 | cons B bs ih=>simp only [flattenMeter,List.flatten_cons,ih]

theorem flatten_work (bs : List (List Nat)) :
 (flattenMeter bs).work=bs.flatten.length+bs.length+1 := by
 induction bs with
 | nil=>simp [flattenMeter]
 | cons B bs ih=>simp only [flattenMeter,ih,List.flatten_cons,List.length_append,List.length_cons];omega
end Universal233.Rule5PendantLocalWork
