/- Contacted repair component: pendant cuts cannot contain a selected endpoint. -/
import CherryEndpointBlocks
open RMAF ForestState Universal233 Universal233.HardParent
open IndependentGeometry IndependentOneExchange ContactedClade
namespace ContactedRepair

theorem root_span_hit {T : Tree} {A : List Nat} (hit : ∃x,x∈leaves T ∧ x∈A) :
 ([] : Vertex)∈rootedSpan A T := by
 cases T with
 | leaf y =>
  obtain ⟨x,hx,ha⟩ := hit
  have eq : x=y := by simpa [leaves] using hx
  subst x
  simp [rootedSpan,ha]
 | node l r =>
  have active := span_active hit.choose_spec.1 hit.choose_spec.2
  simp only [rootedSpan] at active ⊢
  split at active
  · contradiction
  · rename_i no
    simp only [no,ite_false]
    exact List.mem_cons_self

theorem subtree_span_hit {T U : Tree} {p : Vertex} {A : List Nat}
 (sub : CoreGraph.subtree T p=some U) (hit : ∃x,x∈leaves U ∧ x∈A) :
 p∈rootedSpan A T := by
 induction p generalizing T with
 | nil =>
  have eq : T=U := by simpa [CoreGraph.subtree] using sub
  subst T
  exact root_span_hit hit
 | cons side rest ih =>
  cases T with
  | leaf y => simp [CoreGraph.subtree] at sub
  | node l r =>
   have active := span_active (subtree_leaves_own sub hit.choose hit.choose_spec.1) hit.choose_spec.2
   simp only [rootedSpan] at active ⊢
   split at active
   · contradiction
   · rename_i no
     simp only [no,ite_false]
     cases side
     · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨rest,ih sub,rfl⟩))
     · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨rest,ih sub,rfl⟩))

theorem minimal_child_selected {T U : Tree} {p : Vertex} {A : List Nat}
 (sub : CoreGraph.subtree T p=some U) (hit : ∃x,x∈leaves U ∧ x∈A)
 (parent : p.dropLast∈minimalVertices A T) : p∈minimalVertices A T := by
 induction p generalizing T with
 | nil => exact parent
 | cons side rest ih =>
  cases T with
  | leaf y => simp [CoreGraph.subtree] at sub
  | node l r =>
   cases side
   · change CoreGraph.subtree l rest=some U at sub
     have al := span_active (subtree_leaves_own sub hit.choose hit.choose_spec.1) hit.choose_spec.2
     cases er : (rootedSpan A r).isEmpty with
     | false =>
      simp only [minimalVertices,al,er,Bool.false_eq_true,ite_false]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨rest,subtree_span_hit sub hit,rfl⟩))
     | true =>
      rw [minimal_node_left A l r er] at parent ⊢
      cases rest with
      | nil => exact False.elim (root_not_prepend_own false _ parent)
      | cons bit tail =>
       have child : (bit::tail).dropLast∈minimalVertices A l := by
        obtain ⟨w,hw,eq⟩ := List.mem_map.1 parent
        have same : w=(bit::tail).dropLast := by simpa using eq
        exact same ▸ hw
       exact List.mem_map.2 ⟨_,ih sub child,rfl⟩
   · change CoreGraph.subtree r rest=some U at sub
     have ar := span_active (subtree_leaves_own sub hit.choose hit.choose_spec.1) hit.choose_spec.2
     cases el : (rootedSpan A l).isEmpty with
     | false =>
      simp only [minimalVertices,ar,el,Bool.false_eq_true,ite_false]
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨rest,subtree_span_hit sub hit,rfl⟩))
     | true =>
      rw [minimal_node_right A l r el] at parent ⊢
      cases rest with
      | nil => exact False.elim (root_not_prepend_own true _ parent)
      | cons bit tail =>
       have child : (bit::tail).dropLast∈minimalVertices A r := by
        obtain ⟨w,hw,eq⟩ := List.mem_map.1 parent
        have same : w=(bit::tail).dropLast := by simpa using eq
        exact same ▸ hw
       exact List.mem_map.2 ⟨_,ih sub child,rfl⟩

theorem pendant_subtree_absent_endpoints {S U : Tree} {p : Vertex} {a b : Nat}
 (cut : p∈Universal233.CherryBranching.cuts S a b) (sub : CoreGraph.subtree S p=some U) :
 a∉leaves U ∧ b∉leaves U := by
 have flags := (List.mem_filter.1 cut).2
 simp only [Bool.and_eq_true] at flags
 have parent : p.dropLast∈minimalVertices [a,b] S := by
  exact List.contains_iff_mem.1 flags.1.2
 have outside : p∉minimalVertices [a,b] S := by
  simpa using flags.2
 constructor
 · intro ha
   exact outside (minimal_child_selected sub ⟨a,ha,by simp⟩ parent)
 · intro hb
   exact outside (minimal_child_selected sub ⟨b,hb,by simp⟩ parent)
end ContactedRepair
