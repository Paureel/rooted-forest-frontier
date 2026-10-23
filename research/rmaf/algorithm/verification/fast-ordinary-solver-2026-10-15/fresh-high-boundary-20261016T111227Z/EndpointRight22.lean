-- Own symmetric endpoint argument. CherryAt remains the ordered a,b predicate.
import Forest21
open RMAF Universal233
namespace OwnHigh
theorem cherry_b_mem (T : Tree) (p : Vertex) (a b : Nat)
    (hc : CoreGraph.CherryAt T p a b) : b ∈ leaves T := by
  exact subtree_labels_subset T (.node (.leaf a) (.leaf b)) p hc b (by simp [leaves])
theorem cherry_in_rootedSpan_right (T : Tree) (p : Vertex) (a b : Nat) (P : List Nat)
    (hc : CoreGraph.CherryAt T p a b) (hb : b ∈ P) : p ∈ rootedSpan P T := by
  induction p generalizing T with
  | nil =>
    have he : T = .node (.leaf a) (.leaf b) := by
      simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
    subst T
    simp [rootedSpan, hb]
  | cons side p ih =>
    cases T with
    | leaf x => simp [CoreGraph.CherryAt, CoreGraph.subtree] at hc
    | node l r =>
      cases side with
      | false =>
        have hcl : CoreGraph.CherryAt l p a b := by
          simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
        have hne := span_nonempty P l b (cherry_b_mem l p a b hcl) hb
        have hm := ih l hcl
        simpa [rootedSpan, hne, prependSide] using (Or.inl hm : p ∈ rootedSpan P l ∨ false)
      | true =>
        have hcr : CoreGraph.CherryAt r p a b := by
          simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
        have hne := span_nonempty P r b (cherry_b_mem r p a b hcr) hb
        have hm := ih r hcr
        simp [rootedSpan, hne, prependSide, hm]
theorem cherry_in_minimal_right (T : Tree) (p : Vertex) (a b : Nat) (P : List Nat)
    (hc : CoreGraph.CherryAt T p a b) (hb : b ∈ P)
    (hsub : ∀ x ∈ P, x ∈ leaves T) (hmany : ∃ x ∈ P, x ≠ b) :
    p ∈ minimalVertices P T := by
  induction p generalizing T with
  | nil =>
    have he : T = .node (.leaf a) (.leaf b) := by
      simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
    subst T
    obtain ⟨x,hx,hxb⟩ := hmany
    have hxa : x = a ∨ x = b := by simpa [leaves] using hsub x hx
    have ha : a ∈ P := by
      rcases hxa with he | he
      · simpa [he] using hx
      · exact False.elim (hxb he)
    simp [minimalVertices, rootedSpan, ha, hb]
  | cons side p ih =>
    cases T with
    | leaf x => simp [CoreGraph.CherryAt, CoreGraph.subtree] at hc
    | node l r =>
      cases side with
      | false =>
        have hcl : CoreGraph.CherryAt l p a b := by
          simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
        have hl := span_nonempty P l b (cherry_b_mem l p a b hcl) hb
        by_cases hr : (rootedSpan P r).isEmpty = true
        · have hsubl : ∀ x ∈ P, x ∈ leaves l := by
            intro x hx
            rcases List.mem_append.mp (hsub x hx) with hxl | hxr
            · exact hxl
            · exact False.elim ((span_empty_iff P r).mp (List.isEmpty_iff.mp hr) x hxr hx)
          have hm := ih l hcl hsubl
          simpa [minimalVertices, hl, hr, prependSide] using hm
        · have hr' : (rootedSpan P r).isEmpty = false := Bool.eq_false_iff.mpr hr
          have hm := cherry_in_rootedSpan_right l p a b P hcl hb
          simp [minimalVertices, hl, hr', prependSide, hm]
      | true =>
        have hcr : CoreGraph.CherryAt r p a b := by
          simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
        have hr := span_nonempty P r b (cherry_b_mem r p a b hcr) hb
        by_cases hl : (rootedSpan P l).isEmpty = true
        · have hsubr : ∀ x ∈ P, x ∈ leaves r := by
            intro x hx
            rcases List.mem_append.mp (hsub x hx) with hxl | hxr
            · exact False.elim ((span_empty_iff P l).mp (List.isEmpty_iff.mp hl) x hxl hx)
            · exact hxr
          have hm := ih r hcr hsubr
          simpa [minimalVertices, hl, hr, prependSide] using hm
        · have hl' : (rootedSpan P l).isEmpty = false := Bool.eq_false_iff.mpr hl
          have hm := cherry_in_rootedSpan_right r p a b P hcr hb
          simp [minimalVertices, hl', hr, prependSide, hm]
#print axioms cherry_in_minimal_right
end OwnHigh
