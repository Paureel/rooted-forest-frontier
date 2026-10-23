import Runtime01

/-! Reviewer-created original-pair consumer. This instantiates no whole forest
state or live scheduler; it constructs resolved slots from literal pretest output. -/
namespace FreshDepthOneConsumer
open RMAF Universal233 Universal233.DepthOne Universal233.CutRealization

theorem exact_zero_one_or_remaining_two (T S : Tree) (hp : proper T S = true) :
    (∃ c, pretest01 T S = .found c ∧ cutCost c = 0 ∧
      agreement T S (forest S c) = true ∧
      RealizedOutput S ⟨forest S c,sourceCuts c⟩ ∧
      ∀ F, agreement T S F = true → cutCost c ≤ F.length - 1) ∨
    (∃ c, pretest01 T S = .found c ∧ cutCost c = 1 ∧
      agreement T S (forest S c) = true ∧
      RealizedOutput S ⟨forest S c,sourceCuts c⟩ ∧
      ∀ F, agreement T S F = true → cutCost c ≤ F.length - 1) ∨
    (pretest01 T S = .rejected ∧ ∀ F, agreement T S F = true → 2 ≤ F.length - 1) := by
  cases h : pretest01 T S with
  | refused =>
    have impossible := (refused_iff T S).1 h
    simp [hp] at impossible
  | rejected => exact Or.inr (Or.inr ⟨rfl,rejected_lower_bound T S h⟩)
  | found c =>
    have hs := found_original_minimum T S c h
    cases c with
    | none => exact Or.inl ⟨none,rfl,rfl,hs.1,hs.2.1,hs.2.2.2.2⟩
    | some p => exact Or.inr (Or.inl ⟨some p,rfl,rfl,hs.1,hs.2.1,hs.2.2.2.2⟩)

#print axioms exact_zero_one_or_remaining_two
end FreshDepthOneConsumer
