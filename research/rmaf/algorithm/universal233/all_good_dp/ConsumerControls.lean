import ExactMinimum
import DPControls

namespace AllGoodDPConsumerControls
open RMAF ForestState AllGoodDP AllGoodControls

theorem literal_case_for_every_budget (T : Option Tree) (ss : List Tree)
    (h : AllGoodDP.allGood T ss = true) :
    ∃ F, run T ss = some F ∧ agrees T ss F = true ∧
      additionalCost ss F + ss.length = F.length ∧
      ∀ q, additionalCost ss F ≤ q ↔
        ∃ G, agrees T ss G = true ∧ additionalCost ss G ≤ q := by
  obtain ⟨F,hF,hA,hC,hM⟩ := run_total_exact T ss h
  refine ⟨F,hF,hA,hC,?_⟩
  intro q
  constructor
  · intro hq; exact ⟨F,hA,hq⟩
  · rintro ⟨G,hG,hq⟩; exact Nat.le_trans (hM G hG) hq

theorem crossed_budget_boundary :
    decideBudget (some quartet) crossed 0 = false ∧
    decideBudget (some quartet) crossed 1 = true := by decide

theorem six_budget_boundary :
    decideBudget (some six) three 1 = false ∧
    decideBudget (some six) three 2 = true := by decide

theorem none_boundary :
    decideBudget none [] 0 = true ∧ run none [] = some [] := by decide

theorem original_source_offset (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (ha : agrees T ss F = true) : ss.length ≤ F.length ∧
      additionalCost ss F + ss.length = F.length :=
  ⟨sources_le_blocks T ss F ha,additional_exact T ss F ha⟩
end AllGoodDPConsumerControls
