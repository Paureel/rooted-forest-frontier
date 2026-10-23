import CoreProgram

/-! Actual candidate source-code facts. They prove normalization and a
one-cut trace for arbitrary pure source subtrees, not target agreement. -/
namespace ScaffoldProfiles.Source
open RMAF Universal233.CoreProgram

theorem homogeneous_source_normalizes (t : Tree) (color : Nat → Nat) (p : CoreGraph.Vertex)
    (a : Nat) (h : ∀ x ∈ leaves t, color x = a) :
    normalize (fromTree color p t) = .leaf ⟨p, leaves t, a⟩ := by
  induction t generalizing p with
  | leaf x =>
    have hx := h x (by simp [leaves])
    simp [fromTree, normalize, leaves, hx]
  | node l r il ir =>
    have hl : ∀ x ∈ leaves l, color x = a := by
      intro x hx; exact h x (by simp [leaves, hx])
    have hr : ∀ x ∈ leaves r, color x = a := by
      intro x hx; exact h x (by simp [leaves, hx])
    simp [fromTree, normalize, il _ hl, ir _ hr, leaves]

/-- Once original pure subtrees normalize to the two root children, the
actual run detaches the first one at original edge ([] ,[false]). -/
theorem two_root_groups_one_cut (xs ys : List Nat) :
    (run 1 (.node [] (.leaf ⟨[false], xs, 0⟩) (.leaf ⟨[true], ys, 1⟩)) [] []).outputs =
      [⟨[xs,ys], [[false]]⟩] := by
  simp [run, step, normalize, choose, groups, attempt, erase, prefixRoot]

/-- Internal source shapes can be arbitrary while the same profile [1]
remains. The color-purity hypotheses are explicit; no target is mentioned. -/
theorem arbitrary_pure_subtrees_one_cut (l r : Tree) (color : Nat → Nat)
    (hl : ∀ x ∈ leaves l, color x = 0) (hr : ∀ x ∈ leaves r, color x = 1) :
    (run 1 (fromTree color [] (.node l r)) [] []).outputs =
      [⟨[leaves l, leaves r], [[false]]⟩] := by
  have hn : normalize (fromTree color [] (.node l r)) =
      .node [] (.leaf ⟨[false], leaves l, 0⟩) (.leaf ⟨[true], leaves r, 1⟩) := by
    simp [fromTree, normalize, homogeneous_source_normalizes l color [false] 0 hl,
      homogeneous_source_normalizes r color [true] 1 hr]
  simpa [run, step, hn, normalize, choose, groups, attempt, erase, prefixRoot] using
    two_root_groups_one_cut (leaves l) (leaves r)

#print axioms homogeneous_source_normalizes
#print axioms two_root_groups_one_cut
#print axioms arbitrary_pure_subtrees_one_cut
end ScaffoldProfiles.Source
