/- Contacted prover: minimal hulls are monotone under label inclusion. -/
import RestrictionHereditaryV3
open RMAF ForestState Universal233 Universal233.HardParent
open IndependentGeometry IndependentOneExchange
namespace ContactedClade

theorem span_absent (T : Tree) (A : List Nat) (no : ∀x∈leaves T,x∉A) :
 rootedSpan A T=[] := by
 induction T with
 | leaf x => simp [rootedSpan,no x (by simp [leaves])]
 | node l r il ir =>
  have el := il (fun x hx=>no x (List.mem_append_left _ hx))
  have er := ir (fun x hx=>no x (List.mem_append_right _ hx))
  simp [rootedSpan,el,er]

theorem span_empty_mono (T : Tree) {A B : List Nat} (sub : ∀x∈A,x∈B)
 (empty : (rootedSpan B T).isEmpty=true) : (rootedSpan A T).isEmpty=true := by
 have no := span_empty_absent T B empty
 have zero := span_absent T A (fun x hx ha=>no x hx (sub x ha))
 simp [zero]

theorem span_subset (T : Tree) {A B : List Nat} (sub : ∀x∈A,x∈B) :
 ∀v∈rootedSpan A T,v∈rootedSpan B T := by
 induction T with
 | leaf x =>
  by_cases ax : x∈A
  · have bx := sub x ax
    simp [rootedSpan,ax,bx]
  · simp [rootedSpan,ax]
 | node l r il ir =>
  by_cases el : (rootedSpan B l).isEmpty=true
  · by_cases er : (rootedSpan B r).isEmpty=true
    · have al := span_empty_mono l sub el
      have ar := span_empty_mono r sub er
      simp [rootedSpan,el,er,al,ar]
    · simp only [rootedSpan,el,er,Bool.true_and,ite_false]
      split
      · simp
      · intro v hv
        rcases List.mem_cons.1 hv with rfl|hv
        · exact List.mem_cons_self
        · rcases List.mem_append.1 hv with hv|hv
          · obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
            exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨w,il w hw,rfl⟩))
          · obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
            exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨w,ir w hw,rfl⟩))
  · simp only [rootedSpan,el,Bool.false_and,ite_false]
    split
    · simp
    · intro v hv
      rcases List.mem_cons.1 hv with rfl|hv
      · exact List.mem_cons_self
      · rcases List.mem_append.1 hv with hv|hv
        · obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
          exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨w,il w hw,rfl⟩))
        · obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
          exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨w,ir w hw,rfl⟩))

theorem minimal_node_left (A : List Nat) (l r : Tree)
 (er : (rootedSpan A r).isEmpty=true) :
 minimalVertices A (.node l r)=prependSide false (minimalVertices A l) := by
 by_cases el : (rootedSpan A l).isEmpty=true
 · have ml := minimal_empty_if_span l A el
   have mr := minimal_empty_if_span r A er
   simp [minimalVertices,el,er,ml,mr,prependSide]
 · simp [minimalVertices,el,er]

theorem minimal_node_right (A : List Nat) (l r : Tree)
 (el : (rootedSpan A l).isEmpty=true) :
 minimalVertices A (.node l r)=prependSide true (minimalVertices A r) := by
 simp only [minimalVertices,el,ite_true]

theorem minimal_subset (T : Tree) {A B : List Nat} (sub : ∀x∈A,x∈B) :
 ∀v∈minimalVertices A T,v∈minimalVertices B T := by
 induction T with
 | leaf x =>
  by_cases ax : x∈A
  · have bx := sub x ax
    simp [minimalVertices,ax,bx]
  · simp [minimalVertices,ax]
 | node l r il ir =>
  by_cases el : (rootedSpan B l).isEmpty=true
  · have al := span_empty_mono l sub el
    rw [minimal_node_right A l r al,minimal_node_right B l r el]
    intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
    exact List.mem_map.2 ⟨w,ir w hw,rfl⟩
  · by_cases er : (rootedSpan B r).isEmpty=true
    · have ar := span_empty_mono r sub er
      rw [minimal_node_left A l r ar,minimal_node_left B l r er]
      intro v hv
      obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
      exact List.mem_map.2 ⟨w,il w hw,rfl⟩
    · have same : minimalVertices B (.node l r)=rootedSpan B (.node l r) := by
       simp [minimalVertices,rootedSpan,el,er]
      rw [same]
      intro v hv
      exact span_subset (.node l r) sub v (minimal_in_span (.node l r) A v hv)

theorem disjoint_subsets (T : Tree) {A B C D : List Nat}
 (ab : ∀x∈A,x∈B) (cd : ∀x∈C,x∈D)
 (old : disjointVertices (minimalVertices B T) (minimalVertices D T)=true) :
 disjointVertices (minimalVertices A T) (minimalVertices C T)=true := by
 apply List.all_eq_true.2
 intro v hv
 have notin : v∉minimalVertices C T := by
  intro member
  exact disjoint_forbids old (minimal_subset T ab v hv) (minimal_subset T cd v member)
 simpa using notin
end ContactedClade
