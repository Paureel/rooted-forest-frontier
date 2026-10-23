/- Generic subtree boundary geometry, derived directly from the executable hull. -/
import CommonSingletonMerge
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentOneExchange

theorem span_empty_absent (T : Tree) (B : List Nat) (empty : (rootedSpan B T).isEmpty=true) :
 ∀x∈leaves T,x∉B := by
 induction T with
 | leaf y =>
  intro x hx
  have eq : x=y := by simpa [leaves] using hx
  subst x
  simpa [rootedSpan] using empty
 | node l r il ir =>
  have both : (rootedSpan B l).isEmpty=true ∧ (rootedSpan B r).isEmpty=true := by
   unfold rootedSpan at empty
   split at empty
   · simpa only [Bool.and_eq_true] using (by assumption : ((rootedSpan B l).isEmpty && (rootedSpan B r).isEmpty)=true)
   · contradiction
  intro x hx
  rcases List.mem_append.1 hx with hx|hx
  · exact il both.1 x hx
  · exact ir both.2 x hx

theorem span_active {T : Tree} {B : List Nat} {x : Nat} (xt : x∈leaves T) (xb : x∈B) :
 (rootedSpan B T).isEmpty=false := by
 cases h : (rootedSpan B T).isEmpty with
 | false => rfl
 | true => exact False.elim (span_empty_absent T B h x xt xb)

theorem subtree_leaves_own {T U : Tree} {p : Vertex}
 (h : CoreGraph.subtree T p=some U) : ∀x∈leaves U,x∈leaves T := by
 induction p generalizing T with
 | nil =>
  have eq : T=U := by simpa [CoreGraph.subtree] using h
  subst T
  exact fun _ hx=>hx
 | cons side rest ih =>
  cases T with
  | leaf y => simp [CoreGraph.subtree] at h
  | node l r =>
   cases side
   · intro x hx;exact List.mem_append_left _ (ih h x hx)
   · intro x hx;exact List.mem_append_right _ (ih h x hx)

theorem boundary_in_span {T U : Tree} {p : Vertex}
 (h : CoreGraph.subtree T p=some U) (pn : p≠[]) {B : List Nat}
 (hit : ∃x,x∈leaves U ∧ x∈B) : p.dropLast∈rootedSpan B T := by
 induction p generalizing T with
 | nil => exact False.elim (pn rfl)
 | cons side rest ih =>
  cases T with
  | leaf y => simp [CoreGraph.subtree] at h
  | node l r =>
   cases side
   · have left := span_active (subtree_leaves_own h hit.choose_spec.1) hit.choose_spec.2
     simp only [rootedSpan,left,Bool.false_and,Bool.false_eq_true,ite_false]
     cases rest with
     | nil => exact List.mem_cons_self
     | cons bit tail =>
      have child := ih h (by simp) hit
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨_,child,rfl⟩))
   · have right := span_active (subtree_leaves_own h hit.choose_spec.1) hit.choose_spec.2
     simp only [rootedSpan,right,Bool.and_false,Bool.false_eq_true,ite_false]
     cases rest with
     | nil => exact List.mem_cons_self
     | cons bit tail =>
      have child := ih h (by simp) hit
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨_,child,rfl⟩))

theorem crossing_boundary_in_minimal {T U : Tree} {p : Vertex}
 (h : CoreGraph.subtree T p=some U) {B : List Nat}
 (hit : ∃x,x∈leaves U ∧ x∈B)
 (outside : ∃y,y∈leaves T ∧ y∈B ∧ y∉leaves U) :
 p.dropLast∈minimalVertices B T := by
 induction p generalizing T with
 | nil =>
  have eq : T=U := by simpa [CoreGraph.subtree] using h
  subst T
  obtain ⟨y,hy,_,no⟩ := outside
  exact False.elim (no hy)
 | cons side rest ih =>
  cases T with
  | leaf y => simp [CoreGraph.subtree] at h
  | node l r =>
   cases side
   · have left := span_active (subtree_leaves_own h hit.choose_spec.1) hit.choose_spec.2
     cases er : (rootedSpan B r).isEmpty with
     | false =>
      simp only [minimalVertices,left,er,Bool.false_eq_true,ite_false]
      cases rest with
      | nil => exact List.mem_cons_self
      | cons bit tail =>
       have child := boundary_in_span h (by simp) hit
       exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨_,child,rfl⟩))
     | true =>
      obtain ⟨y,hy,yB,no⟩ := outside
      have yl : y∈leaves l := by
       rcases List.mem_append.1 hy with yl|yr
       · exact yl
       · exact False.elim (span_empty_absent r B er y yr yB)
      have child := ih h hit ⟨y,yl,yB,no⟩
      cases rest with
      | nil =>
       have eq : l=U := by simpa [CoreGraph.subtree] using h
       exact False.elim (no (eq ▸ yl))
      | cons bit tail =>
       simp only [minimalVertices,left,er,Bool.false_eq_true,ite_false,ite_true]
       exact List.mem_map.2 ⟨_,child,rfl⟩
   · have right := span_active (subtree_leaves_own h hit.choose_spec.1) hit.choose_spec.2
     cases el : (rootedSpan B l).isEmpty with
     | false =>
      simp only [minimalVertices,right,el,Bool.false_eq_true,ite_false]
      cases rest with
      | nil => exact List.mem_cons_self
      | cons bit tail =>
       have child := boundary_in_span h (by simp) hit
       exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨_,child,rfl⟩))
     | true =>
      obtain ⟨y,hy,yB,no⟩ := outside
      have yr : y∈leaves r := by
       rcases List.mem_append.1 hy with yl|yr
       · exact False.elim (span_empty_absent l B el y yl yB)
       · exact yr
      have child := ih h hit ⟨y,yr,yB,no⟩
      cases rest with
      | nil =>
       have eq : r=U := by simpa [CoreGraph.subtree] using h
       exact False.elim (no (eq ▸ yr))
      | cons bit tail =>
       simp only [minimalVertices,el,ite_true]
       exact List.mem_map.2 ⟨_,child,rfl⟩
end IndependentOneExchange
