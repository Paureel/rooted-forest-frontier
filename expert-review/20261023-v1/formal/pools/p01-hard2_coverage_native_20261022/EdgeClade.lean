import CollapseParent
open RMAF VertexGeometry Universal233
namespace ContactedHard2Survival

theorem edge_child_subtree (T : Tree) (e : RMAF.Vertex×RMAF.Vertex) (member : e∈PairGeometry.edges T) :
 ∃U,CoreGraph.subtree T e.2=some U := by
 induction T generalizing e with
 | leaf x=>simp only [PairGeometry.edges,List.not_mem_nil] at member
 | node l r ihl ihr=>
  simp only [PairGeometry.edges,List.mem_cons,List.mem_append,List.mem_map] at member
  rcases member with eq|eq|left|right
  · subst e;exact ⟨l,rfl⟩
  · subst e;exact ⟨r,rfl⟩
  · obtain ⟨f,mem,eq⟩:=left
    subst e
    obtain ⟨U,sub⟩:=ihl f mem
    exact ⟨U,sub⟩
  · obtain ⟨f,mem,eq⟩:=right
    subst e
    obtain ⟨U,sub⟩:=ihr f mem
    exact ⟨U,sub⟩

theorem subtree_append_own (T : Tree) (p q : RMAF.Vertex) :
 CoreGraph.subtree T (p++q)=(CoreGraph.subtree T p).bind (fun U=>CoreGraph.subtree U q) := by
 induction p generalizing T with
 | nil=>rfl
 | cons b p ih=>
  cases T with
  | leaf x=>rfl
  | node l r=>cases b <;>exact ih _

theorem singleton_selected_leafAt (T : Tree) (x : Nat) (a : RMAF.Vertex) (selected : selectedLeaves [x] T a) :
 CoreGraph.LeafAt T a x := by
 induction T generalizing a with
 | leaf y=>
  have eq:=selected.1
  have same : y=x := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using selected.2
  subst a;subst y;rfl
 | node l r ihl ihr=>
  cases a with
  | nil=>exact False.elim selected
  | cons b a=>
   cases b with
   | false=>exact ihl a selected
   | true=>exact ihr a selected

theorem selected_singleton_exists_own (T : Tree) (x : Nat) (member : x∈leaves T) :
 ∃a,selectedLeaves [x] T a := by
 induction T with
 | leaf y=>
  have eq : x=y := by simpa only [leaves,List.mem_cons,List.not_mem_nil,or_false] using member
  subst x
  exact ⟨[],rfl,List.mem_cons_self⟩
 | node l r ihl ihr=>
  rcases List.mem_append.mp member with ml|mr
  · obtain ⟨a,ha⟩:=ihl ml
    exact ⟨false::a,ha⟩
  · obtain ⟨a,ha⟩:=ihr mr
    exact ⟨true::a,ha⟩

theorem leafAt_label_own (T : Tree) (a : RMAF.Vertex) (x : Nat) (atLeaf : CoreGraph.LeafAt T a x) : x∈leaves T := by
 induction a generalizing T with
 | nil=>
  have eq : T=.leaf x := Option.some.inj atLeaf
  subst T;exact List.mem_cons_self
 | cons b a ih=>
  cases T with
  | leaf y=>cases atLeaf
  | node l r=>
   cases b with
   | false=>exact List.mem_append_left _ (ih l atLeaf)
   | true=>exact List.mem_append_right _ (ih r atLeaf)

theorem selected_subtree_transport (T U : Tree) (p a : RMAF.Vertex) (x : Nat)
 (sub : CoreGraph.subtree T p=some U) (atLeaf : selectedLeaves [x] U a) : selectedLeaves [x] T (p++a) := by
 induction p generalizing T with
 | nil=>have eq : T=U:=Option.some.inj sub;subst T;exact atLeaf
 | cons b p ih=>
  cases T with
  | leaf y=>cases sub
  | node l r=>
   cases b with
   | false=>exact ih l sub
   | true=>exact ih r sub

theorem descendants_child_clade (T U : Tree) (p : RMAF.Vertex) (nd : (leaves T).Nodup)
 (sub : CoreGraph.subtree T p=some U) : ∀x,x∈PairGeometry.descendants T p ↔ x∈leaves U := by
 intro x
 rw [PairGeometry.descendants_mem]
 constructor
 · intro h
   obtain ⟨a,ha⟩:=selected_singleton_exists_own T x h.1
   have address:=PairGeometry.leafAddress_correct T x nd a ha
   rw [address] at h
   obtain ⟨q,eq⟩:=h.2
   have leaf:=singleton_selected_leafAt T x a ha
   change CoreGraph.subtree T a=some (.leaf x) at leaf
   rw [eq,subtree_append_own,sub,Option.bind_some] at leaf
   exact leafAt_label_own U q x leaf
 · intro member
   obtain ⟨a,ha⟩:=selected_singleton_exists_own U x member
   have big:=selected_subtree_transport T U p a x sub ha
   have address:=PairGeometry.leafAddress_correct T x nd (p++a) big
   exact ⟨leafAt_label_own T (p++a) x (singleton_selected_leafAt T x (p++a) big),by rw [address];exact ⟨a,rfl⟩⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.edge_child_subtree
#print axioms ContactedHard2Survival.edge_child_subtree
#check @ContactedHard2Survival.subtree_append_own
#print axioms ContactedHard2Survival.subtree_append_own
#check @ContactedHard2Survival.singleton_selected_leafAt
#print axioms ContactedHard2Survival.singleton_selected_leafAt
#check @ContactedHard2Survival.selected_singleton_exists_own
#print axioms ContactedHard2Survival.selected_singleton_exists_own
#check @ContactedHard2Survival.leafAt_label_own
#print axioms ContactedHard2Survival.leafAt_label_own
#check @ContactedHard2Survival.selected_subtree_transport
#print axioms ContactedHard2Survival.selected_subtree_transport
#check @ContactedHard2Survival.descendants_child_clade
#print axioms ContactedHard2Survival.descendants_child_clade
