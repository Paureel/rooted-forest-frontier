import CoarsenHullV4
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentGeometry

theorem minimal_empty_if_span (T : Tree) (B : List Nat) (h : (rootedSpan B T).isEmpty=true) :
 minimalVertices B T=[] := by
 have empty : rootedSpan B T=[] := by simpa using h
 cases hm : minimalVertices B T with
 | nil => rfl
 | cons v rest =>
  have member := minimal_in_span T B v (by simp [hm])
  simp [empty] at member

theorem minimal_shrink_lift {a b z : Nat} {C T : Tree} (h : Grow a b z C T)
 (ab : a≠b) (B : List Nat) (nz : z∉B) :
 ∀v∈minimalVertices (shrinkBlock a b z B) C,embed a C T v∈minimalVertices B T := by
 induction h with
 | @fixed x xa xb xz =>
  have sf : x∈shrinkBlock a b z B ↔ x∈B := by
   simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 (shrink_fixed_contains B xa xb xz)
  by_cases hx : x∈B <;> simp [minimalVertices,sf,hx,embed]
 | cherry =>
  have sm : z∈shrinkBlock a b z B ↔ a∈B := by
   simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 (shrink_z_contains B ab nz)
  by_cases ha : a∈B <;> by_cases hb : b∈B <;> simp [minimalVertices,rootedSpan,sm,ha,hb,embed,prependSide]
 | swapped =>
  have sm : z∈shrinkBlock a b z B ↔ a∈B := by
   simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 (shrink_z_contains B ab nz)
  by_cases ha : a∈B <;> by_cases hb : b∈B <;> simp [minimalVertices,rootedSpan,sm,ha,hb,embed,prependSide,Ne.symm ab]
 | @node l r L R hl hr il ir =>
  have el := empty_from_map (embed a l L) _ _ (span_shrink_lift hl ab B nz)
  have er := empty_from_map (embed a r R) _ _ (span_shrink_lift hr ab B nz)
  by_cases eL : (rootedSpan B L).isEmpty=true
  · have cl := el eL
    simp only [minimalVertices,eL,cl,ite_true]
    intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
    exact List.mem_map.2 ⟨embed a r R w,ir w hw,rfl⟩
  · by_cases eR : (rootedSpan B R).isEmpty=true
    · have cr := er eR
      have mr := minimal_empty_if_span r (shrinkBlock a b z B) cr
      simp only [minimalVertices,eL,eR,cr,ite_true,ite_false]
      split
      · simp [mr,prependSide]
      · intro v hv
        obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
        exact List.mem_map.2 ⟨embed a l L w,il w hw,rfl⟩
    · simp only [minimalVertices,eL,eR,ite_false]
      split
      · intro v hv
        obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
        have old := minimal_in_span R B (embed a r R w) (ir w hw)
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨embed a r R w,old,rfl⟩))
      · split
        · intro v hv
          obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
          have old := minimal_in_span L B (embed a l L w) (il w hw)
          exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨embed a l L w,old,rfl⟩))
        · intro v hv
          rcases List.mem_cons.1 hv with rfl|hv
          · simp [embed]
          · rcases List.mem_append.1 hv with hv|hv
            · obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
              exact List.mem_cons_of_mem _ (List.mem_append_left _
               (List.mem_map.2 ⟨embed a l L w,span_shrink_lift hl ab B nz w hw,rfl⟩))
            · obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
              exact List.mem_cons_of_mem _ (List.mem_append_right _
               (List.mem_map.2 ⟨embed a r R w,span_shrink_lift hr ab B nz w hw,rfl⟩))
end IndependentGeometry
