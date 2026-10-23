import CherryForward

namespace ForestState
open RMAF RestrictionBridge

theorem no_selection (t : Tree) (U : List Nat) (hn : ∀ x ∈ leaves t, x ∉ U) :
    rootedSpan U t = [] ∧ minimalVertices U t = [] := by
  induction t with
  | leaf x => have hx := hn x (by simp [leaves]); simp [rootedSpan,minimalVertices,hx]
  | node l r hl hr =>
    have il := hl (fun x hx => hn x (by simp [leaves,hx]))
    have ir := hr (fun x hx => hn x (by simp [leaves,hx]))
    simp [rootedSpan,minimalVertices,il,ir,prependSide]

theorem singleton_no_selection (t : Tree) (a : Nat) (hn : a ∉ leaves t) :
    rootedSpan [a] t = [] ∧ minimalVertices [a] t = [] := by
  apply no_selection
  intro x hx he
  have hxa : x = a := by simpa using he
  subst x
  exact hn hx

theorem singleton_span_nonempty (t : Tree) (a : Nat) (ha : a ∈ leaves t) :
    (rootedSpan [a] t).isEmpty = false := by
  obtain ⟨u,hu⟩ := restriction_exists t [a] ⟨a,ha,by simp⟩
  rw [span_empty,hu]
  rfl

theorem singleton_clear (t : Tree) (a : Nat) (B : List Nat) (nd : (leaves t).Nodup)
    (hn : a ∉ B) :
    Clear (minimalVertices [a] t) (rootedSpan B t) ∧
    Clear (minimalVertices [a] t) (minimalVertices B t) := by
  induction t with
  | leaf x =>
    by_cases hx : x = a
    · subst x; simp [minimalVertices,rootedSpan,hn]
    · simp [minimalVertices,rootedSpan,hx]
  | node l r hl hr =>
    have ndl : (leaves l).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have ndr : (leaves r).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    by_cases hal : a ∈ leaves l
    · have har : a ∉ leaves r := by
        intro hm
        have hc := List.nodup_iff_count.1 nd a
        have hp := List.count_pos_iff.2 hal
        have hq := List.count_pos_iff.2 hm
        simp only [leaves,List.count_append] at hc
        omega
      have er := singleton_no_selection r a har
      have ne := singleton_span_nonempty l a hal
      have il := hl ndl
      cases bl : (rootedSpan B l).isEmpty <;> cases br : (rootedSpan B r).isEmpty
      all_goals simp_all [minimalVertices,rootedSpan,clear_symm (minimalVertices [a] l)]
    · have el := singleton_no_selection l a hal
      by_cases har : a ∈ leaves r
      · have ne := singleton_span_nonempty r a har
        have ir := hr ndr
        cases bl : (rootedSpan B l).isEmpty <;> cases br : (rootedSpan B r).isEmpty
        all_goals simp_all [minimalVertices,rootedSpan,clear_symm (minimalVertices [a] r)]
      · have er := singleton_no_selection r a har
        simp [minimalVertices,el,er,prependSide]

end ForestState
