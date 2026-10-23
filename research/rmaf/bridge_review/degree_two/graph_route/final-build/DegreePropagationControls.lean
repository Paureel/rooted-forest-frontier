import DegreePropagation
import GraphRouteControls
namespace DegreeTwoGraphControls
open RMAF BridgeReview LeastEmbedding DegreeTwoGraph

theorem edge_correct (x y : Vertex) : edge x y = true ↔ Adj x y := by
  simp only [edge, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inl ⟨false,h⟩
    · exact Or.inl ⟨true,h⟩
    · exact Or.inr ⟨false,h⟩
    · exact Or.inr ⟨true,h⟩
  · rintro (⟨b,h⟩ | ⟨b,h⟩)
    · cases b
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
    · cases b
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem component_degree_control :
    ExactTwo (fun z => z ∈ minimalVertices [0,2,3] globalT) [false] := by
  refine ⟨[],[false,false],by decide,by decide,?_,by decide,?_,?_⟩
  · exact Or.inr ⟨false,rfl⟩
  · exact Or.inl ⟨false,rfl⟩
  · intro x hx he
    have all : (minimalVertices [0,2,3] globalT).all
        (fun z => !(edge [false] z) || z == [] || z == [false,false]) = true := by decide
    have hxall := List.all_eq_true.mp all x hx
    have hedge := (edge_correct [false] x).mpr he
    simpa [hedge, Bool.or_eq_true] using hxall

theorem propagated_actual_control :
    ExactTwo (fun z => z ∈ minimalVertices [0,2] globalT) [false] := by
  exact actual_degree_propagation [0,2] [0,2,3] globalT [false]
    (by intro x hx; simp at hx ⊢; rcases hx with h | h <;> simp [h])
    (by decide) (by decide) component_degree_control

theorem singleton_no_two_neighbors :
    ¬ HasTwo (fun z => z ∈ minimalVertices [0] rootT) [false] := by
  rintro ⟨a,b,hab,ha,_,hb,_⟩
  have ha' : a = [false] := by simpa [minimalVertices,rootT,rootedSpan,prependSide] using ha
  have hb' : b = [false] := by simpa [minimalVertices,rootT,rootedSpan,prependSide] using hb
  exact hab (ha'.trans hb'.symm)

#print axioms edge_correct
#print axioms component_degree_control
#print axioms propagated_actual_control
#print axioms singleton_no_two_neighbors
end DegreeTwoGraphControls
