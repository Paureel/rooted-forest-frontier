/- Contacted repair component: the surviving source core separates the endpoints. -/
import PendantHullCoverV2
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade
namespace ContactedRepair

theorem span_prepend (D : List Nat) (l r : Tree) (side : Bool) (v : Vertex)
 (member : v∈rootedSpan D (if side then r else l)) :
 side::v∈rootedSpan D (.node l r) := by
 obtain ⟨U,sub,hit⟩ := span_subtree_hit member
 exact subtree_span_hit sub hit

theorem clean_of_disjoint_span (T : Tree) {A D : List Nat}
 (no : ∀v∈minimalVertices A T,v∉rootedSpan D T) : Clean A D T := by
 induction T with
 | leaf x =>
  intro xa xd
  exact no [] (by simp [minimalVertices,xa]) (by simp [rootedSpan,xd])
 | node l r il ir =>
  by_cases el : (rootedSpan A l).isEmpty=true
  · refine Or.inr (Or.inl ⟨span_empty_absent l A el,ir ?_⟩)
    intro v hv hd
    have parent : true::v∈minimalVertices A (.node l r) := by
     rw [minimal_node_right A l r el]
     exact List.mem_map.2 ⟨v,hv,rfl⟩
    exact no _ parent (span_prepend D l r true v hd)
  · by_cases er : (rootedSpan A r).isEmpty=true
    · refine Or.inl ⟨span_empty_absent r A er,il ?_⟩
      intro v hv hd
      have parent : false::v∈minimalVertices A (.node l r) := by
       rw [minimal_node_left A l r er]
       exact List.mem_map.2 ⟨v,hv,rfl⟩
      exact no _ parent (span_prepend D l r false v hd)
    · refine Or.inr (Or.inr ?_)
      intro x hx xd
      have root : ([] : Vertex)∈minimalVertices A (.node l r) := by
       simp only [minimalVertices,el,er,ite_false]
       exact List.mem_cons_self
      exact no [] root (root_span_hit ⟨x,hx,xd⟩)

theorem source_core_clean (S : Tree) (a b : Nat) :
 Clean [a,b] (coreRemainder S a b) S :=
 clean_of_disjoint_span S (core_remainder_avoids_span S a b)

theorem restrict_leaves_eq (T : Tree) (A : List Nat) :
 optionLeaves (restrict A T)=(leaves T).filter A.contains := by
 induction T with
 | leaf x => cases h : A.contains x <;> simp only [restrict,leaves,h,optionLeaves,List.filter_cons,List.filter_nil,Bool.false_eq_true,ite_false,ite_true]
 | node l r il ir =>
  change optionLeaves (merge (restrict A l) (restrict A r))=_
  rw [option_leaves_merge,il,ir]
  exact (List.filter_append).symm
end ContactedRepair
