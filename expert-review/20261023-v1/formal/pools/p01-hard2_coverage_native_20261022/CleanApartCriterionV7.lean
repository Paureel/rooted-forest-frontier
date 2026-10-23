import CleanApartBasicsV6
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair
namespace ContactedSource

theorem disjoint_clean (T : Tree) (A B : List Nat)
 (h : disjointVertices (minimalVertices A T) (minimalVertices B T)=true) :
 Clean A B T ∨ Clean B A T := by
 induction T with
 | leaf x =>
  apply Or.inl
  intro ax bx
  have am : ([] : Vertex)∈minimalVertices A (.leaf x) := by simp only [minimalVertices,List.contains_iff_mem,ax,ite_true,List.mem_singleton]
  have bm : ([] : Vertex)∈minimalVertices B (.leaf x) := by simp only [minimalVertices,List.contains_iff_mem,bx,ite_true,List.mem_singleton]
  exact disjoint_forbids h am bm
 | node l r il ir =>
  by_cases al : (rootedSpan A l).isEmpty=true
  · by_cases bl : (rootedSpan B l).isEmpty=true
    · rw [minimal_node_right A l r al,minimal_node_right B l r bl] at h
      rcases ir (disjoint_unprepend true h) with cl|cl
      · exact Or.inl (Or.inr (Or.inl ⟨span_empty_absent l A al,cl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨span_empty_absent l B bl,cl⟩))
    · by_cases br : (rootedSpan B r).isEmpty=true
      · exact Or.inl (Or.inr (Or.inl ⟨span_empty_absent l A al,
         clean_absent_D r (span_empty_absent r B br)⟩))
      · rw [minimal_eq_span B l r bl br] at h
        exact Or.inl (clean_of_disjoint_span _ ((disjoint_iff _ _).1 h))
  · by_cases ar : (rootedSpan A r).isEmpty=true
    · by_cases br : (rootedSpan B r).isEmpty=true
      · rw [minimal_node_left A l r ar,minimal_node_left B l r br] at h
        rcases il (disjoint_unprepend false h) with cl|cl
        · exact Or.inl (Or.inl ⟨span_empty_absent r A ar,cl⟩)
        · exact Or.inr (Or.inl ⟨span_empty_absent r B br,cl⟩)
      · by_cases bl : (rootedSpan B l).isEmpty=true
        · exact Or.inl (Or.inl ⟨span_empty_absent r A ar,
           clean_absent_D l (span_empty_absent l B bl)⟩)
        · rw [minimal_eq_span B l r bl br] at h
          exact Or.inl (clean_of_disjoint_span _ ((disjoint_iff _ _).1 h))
    · rw [minimal_eq_span A l r al ar] at h
      exact Or.inr (clean_of_disjoint_span _ ((disjoint_iff _ _).1 (disjoint_sym h)))

theorem clean_disjoint (T : Tree) {A B : List Nat}
 (h : Clean A B T ∨ Clean B A T) :
 disjointVertices (minimalVertices A T) (minimalVertices B T)=true := by
 rcases h with h|h
 · apply (disjoint_iff _ _).2
   intro v hv hb
   exact clean_span_disjoint T h v hv (minimal_in_span T B v hb)
 · apply disjoint_sym
   apply (disjoint_iff _ _).2
   intro v hv ha
   exact clean_span_disjoint T h v hv (minimal_in_span T A v ha)

theorem hull_disjoint_restrict {T R : Tree} {Y A B : List Nat}
 (subA : ∀x∈A,x∈Y) (subB : ∀x∈B,x∈Y) (restrictY : restrict Y T=some R) :
 disjointVertices (minimalVertices A T) (minimalVertices B T)=true ↔
 disjointVertices (minimalVertices A R) (minimalVertices B R)=true := by
 constructor
 · intro h
   have apart := disjoint_clean T A B h
   apply clean_disjoint R
   rcases apart with h|h
   · exact Or.inl ((clean_restrict T Y A B subA subB R restrictY).1 h)
   · exact Or.inr ((clean_restrict T Y B A subB subA R restrictY).1 h)
 · intro h
   have apart := disjoint_clean R A B h
   apply clean_disjoint T
   rcases apart with h|h
   · exact Or.inl ((clean_restrict T Y A B subA subB R restrictY).2 h)
   · exact Or.inr ((clean_restrict T Y B A subB subA R restrictY).2 h)
end ContactedSource

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedSource.disjoint_clean
#print axioms ContactedSource.disjoint_clean
#check @ContactedSource.clean_disjoint
#print axioms ContactedSource.clean_disjoint
#check @ContactedSource.hull_disjoint_restrict
#print axioms ContactedSource.hull_disjoint_restrict
