/- Contacted repair component: core remainder paths avoid the endpoint hull. -/
import LiteralPendantSidesV2
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade
namespace ContactedRepair

theorem lookup_vertex {S U : Tree} {p : Vertex} (sub : CoreGraph.subtree S p=some U) : p∈vertices S := by
 induction p generalizing S with
 | nil => cases S <;> simp [vertices]
 | cons side rest ih =>
  cases S with
  | leaf y => simp [CoreGraph.subtree] at sub
  | node l r =>
   cases side
   · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨rest,ih sub,rfl⟩))
   · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨rest,ih sub,rfl⟩))

theorem span_leaf_selected {S : Tree} {p : Vertex} {x : Nat} {A : List Nat}
 (sub : CoreGraph.subtree S p=some (.leaf x)) (member : p∈rootedSpan A S) : x∈A := by
 induction p generalizing S with
 | nil =>
  have eq : S=Tree.leaf x := by simpa [CoreGraph.subtree] using sub
  subst S
  simpa [rootedSpan] using member
 | cons side rest ih =>
  cases S with
  | leaf y => simp [rootedSpan] at member
  | node l r => cases side <;> exact ih sub (span_child A l r _ _ member)

theorem span_subtree_hit {S : Tree} {p : Vertex} {D : List Nat}
 (member : p∈rootedSpan D S) : ∃U,CoreGraph.subtree S p=some U ∧ ∃x,x∈leaves U ∧ x∈D := by
 classical
 induction p generalizing S with
 | nil =>
  refine ⟨S,rfl,?_⟩
  apply Classical.byContradiction
  intro no
  have absent : ∀x∈leaves S,x∉D := fun x hx hd=>no ⟨x,hx,hd⟩
  have zero := span_absent S D absent
  simp [zero] at member
 | cons side rest ih =>
  cases S with
  | leaf y => simp [rootedSpan] at member
  | node l r => cases side <;> exact ih (span_child D l r _ _ member)

theorem boundary_of_missing_child {S U : Tree} {p : Vertex} (side : Bool) {a b : Nat}
 (sub : CoreGraph.subtree S (p++[side])=some U)
 (parent : p∈minimalVertices [a,b] S)
 (outside : p++[side]∉minimalVertices [a,b] S) : p++[side]∈cuts S a b := by
 apply List.mem_filter.2
 refine ⟨lookup_vertex sub,?_⟩
 simp only [Bool.and_eq_true]
 refine ⟨⟨by simp,?_⟩,?_⟩
 · simpa only [List.dropLast_concat,List.contains_iff_mem] using parent
 · simpa using outside

theorem hull_descendant_cover (S : Tree) (a b : Nat) (U : Tree) :
 ∀p,CoreGraph.subtree S p=some U→p∈minimalVertices [a,b] S→
 ∀x∈leaves U,x∈[a,b] ∨ ∃q∈cuts S a b,x∈subtreeLabels S q := by
 induction U with
 | leaf y =>
  intro p sub parent x hx
  have eq : x=y := by simpa [leaves] using hx
  subst x
  exact Or.inl (span_leaf_selected sub (minimal_in_span S [a,b] p parent))
 | node l r il ir =>
  intro p sub parent x hx
  rcases List.mem_append.1 hx with xl|xr
  · have left : CoreGraph.subtree S (p++[false])=some l := by rw [subtree_append,sub];rfl
    by_cases member : p++[false]∈minimalVertices [a,b] S
    · exact il _ left member x xl
    · exact Or.inr ⟨_,boundary_of_missing_child false left parent member,by rw [subtree_labels_lookup left];exact xl⟩
  · have right : CoreGraph.subtree S (p++[true])=some r := by rw [subtree_append,sub];rfl
    by_cases member : p++[true]∈minimalVertices [a,b] S
    · exact ir _ right member x xr
    · exact Or.inr ⟨_,boundary_of_missing_child true right parent member,by rw [subtree_labels_lookup right];exact xr⟩

def coreRemainder (S : Tree) (a b : Nat) :=
 (coreLabels S a b).filter (fun x=>x != a && x != b)

theorem core_remainder_avoids_span (S : Tree) (a b : Nat) :
 ∀v∈minimalVertices [a,b] S,v∉rootedSpan (coreRemainder S a b) S := by
 intro v hv span
 obtain ⟨U,sub,x,hx,xd⟩ := span_subtree_hit span
 have d := List.mem_filter.1 xd
 have ne : x≠a ∧ x≠b := by simpa only [Bool.and_eq_true,bne_iff_ne] using d.2
 rcases hull_descendant_cover S a b U v sub hv x hx with endpoint|boundary
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at endpoint
   exact endpoint.elim ne.1 ne.2
 · obtain ⟨q,qcut,xq⟩ := boundary
   have absent : x∉((cuts S a b).map (subtreeLabels S)).flatten := by
    simpa using (List.mem_filter.1 d.1).2
   exact absent (List.mem_flatten.2 ⟨_,List.mem_map.2 ⟨q,qcut,rfl⟩,xq⟩)
end ContactedRepair
