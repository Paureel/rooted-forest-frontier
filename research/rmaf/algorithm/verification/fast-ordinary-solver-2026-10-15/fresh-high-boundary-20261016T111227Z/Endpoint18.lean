-- Own endpoint collision geometry; no existing cherry/forest theorem reused.
import Geometry17
open RMAF Universal233
namespace OwnHigh
theorem cherry_in_minimal (T : Tree) (p : Vertex) (a b : Nat) (P : List Nat)
    (hc : CoreGraph.CherryAt T p a b) (ha : a ∈ P)
    (hsub : ∀ x ∈ P, x ∈ leaves T) (hmany : ∃ x ∈ P, x ≠ a) :
    p ∈ minimalVertices P T := by
  induction p generalizing T with
  | nil =>
    have he : T = .node (.leaf a) (.leaf b) := by
      simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
    subst T
    obtain ⟨x,hx,hxa⟩ := hmany
    have hxb : x = a ∨ x = b := by simpa [leaves] using hsub x hx
    have hb : b ∈ P := by
      rcases hxb with he | he
      · exact False.elim (hxa he)
      · simpa [he] using hx
    simp [minimalVertices, rootedSpan, ha, hb]
  | cons side p ih =>
    cases T with
    | leaf x => simp [CoreGraph.CherryAt, CoreGraph.subtree] at hc
    | node l r =>
      cases side with
      | false =>
        have hcl : CoreGraph.CherryAt l p a b := by
          simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
        have hl := span_nonempty P l a (cherry_a_mem l p a b hcl) ha
        by_cases hr : (rootedSpan P r).isEmpty = true
        · have hsubl : ∀ x ∈ P, x ∈ leaves l := by
            intro x hx
            rcases List.mem_append.mp (hsub x hx) with hxl | hxr
            · exact hxl
            · exact False.elim ((span_empty_iff P r).mp (List.isEmpty_iff.mp hr) x hxr hx)
          have hm := ih l hcl hsubl
          simpa [minimalVertices, hl, hr, prependSide] using hm
        · have hr' : (rootedSpan P r).isEmpty = false := Bool.eq_false_iff.mpr hr
          have hm := cherry_in_rootedSpan l p a b P hcl ha
          simp [minimalVertices, hl, hr', prependSide, hm]
      | true =>
        have hcr : CoreGraph.CherryAt r p a b := by
          simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
        have hr := span_nonempty P r a (cherry_a_mem r p a b hcr) ha
        by_cases hl : (rootedSpan P l).isEmpty = true
        · have hsubr : ∀ x ∈ P, x ∈ leaves r := by
            intro x hx
            rcases List.mem_append.mp (hsub x hx) with hxl | hxr
            · exact False.elim ((span_empty_iff P l).mp (List.isEmpty_iff.mp hl) x hxl hx)
            · exact hxr
          have hm := ih r hcr hsubr
          simpa [minimalVertices, hl, hr, prependSide] using hm
        · have hl' : (rootedSpan P l).isEmpty = false := Bool.eq_false_iff.mpr hl
          have hm := cherry_in_rootedSpan r p a b P hcr ha
          simp [minimalVertices, hl', hr, prependSide, hm]
#print axioms cherry_in_minimal
end OwnHigh
