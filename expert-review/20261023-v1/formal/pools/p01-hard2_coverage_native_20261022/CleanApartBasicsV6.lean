/- Original hull disjointness expressed by clean separation. Contacted proof. -/
import SlimCandidateKnownFieldsV3R4
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair
namespace ContactedSource

theorem disjoint_iff (L R : List Vertex) : disjointVertices L R=true ↔ ∀v∈L,v∉R := by
 constructor
 · intro h v hv;exact fun hr=>disjoint_forbids h hv hr
 · intro h;apply List.all_eq_true.2;intro v hv;simpa using h v hv

theorem disjoint_sym {L R : List Vertex} (h : disjointVertices L R=true) :
 disjointVertices R L=true :=
 (disjoint_iff R L).2 (fun v hv hl=>disjoint_forbids h hl hv)

theorem disjoint_unprepend {L R : List Vertex} (s : Bool)
 (h : disjointVertices (prependSide s L) (prependSide s R)=true) :
 disjointVertices L R=true := by
 apply (disjoint_iff L R).2
 intro v hv hr
 exact disjoint_forbids h (List.mem_map.2 ⟨v,hv,rfl⟩) (List.mem_map.2 ⟨v,hr,rfl⟩)

theorem minimal_eq_span (A : List Nat) (l r : Tree)
 (al : ¬(rootedSpan A l).isEmpty=true) (ar : ¬(rootedSpan A r).isEmpty=true) :
 minimalVertices A (.node l r)=rootedSpan A (.node l r) := by
 have el : (rootedSpan A l).isEmpty=false := by
  cases h : (rootedSpan A l).isEmpty
  · rfl
  · exact False.elim (al h)
 have er : (rootedSpan A r).isEmpty=false := by
  cases h : (rootedSpan A r).isEmpty
  · rfl
  · exact False.elim (ar h)
 simp only [minimalVertices,rootedSpan,el,er,Bool.false_and,Bool.false_eq_true,ite_false]

end ContactedSource

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedSource.disjoint_iff
#print axioms ContactedSource.disjoint_iff
#check @ContactedSource.disjoint_sym
#print axioms ContactedSource.disjoint_sym
#check @ContactedSource.disjoint_unprepend
#print axioms ContactedSource.disjoint_unprepend
#check @ContactedSource.minimal_eq_span
#print axioms ContactedSource.minimal_eq_span
