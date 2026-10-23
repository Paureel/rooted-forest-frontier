import LocalCongruence
import ForestMinimumCompletion
namespace GenericForest.LocalIH
open RMAF ForestState ForestMinCompletion

/-- The unchanged actual forest program needs ordinary correctness only at
budgets at most K. The mathematical completion is existential erased proof
support and is eliminated using actual executable callback locality. -/
theorem exact_at_budget_bound
    (K : Nat) (actual : Tree → Tree → Nat → Option Forest)
    (localIH : LocalOrdinaryIH K actual) :
    (∀ T ss q F, q ≤ K → solve actual T ss q = some F →
      agrees T ss F = true ∧ additionalCost ss F ≤ q) ∧
    (∀ T ss q G, q ≤ K → agrees T ss G = true → additionalCost ss G ≤ q →
      ∃ F, solve actual T ss q = some F ∧ F.length ≤ G.length) := by
  obtain ⟨completed,hcompleted,heq⟩ := ordinaryIH_extension localIH
  have globalExact := exact_of_ordinary completed hcompleted
  have programEq (T : Option Tree) (ss : List Tree) (q : Nat) (hq : q ≤ K) :
      solve completed T ss q = solve actual T ss q :=
    solve_congr_budget completed actual q
      (fun t s b hb => heq t s b (Nat.le_trans hb hq)) T ss
  refine ⟨fun T ss q F _ answer => solve_sound actual T ss q F answer,?_⟩
  intro T ss q G hq ha budget
  obtain ⟨F,hF,least⟩ := globalExact.2 T ss q G ha budget
  exact ⟨F,by rw [←programEq T ss q hq]; exact hF,least⟩

/-- Direct current-budget interface for a future well-founded ordinary caller.
No ordinary callback above the current forest budget is assumed correct. -/
theorem exact_at_current_budget
    (actual : Tree → Tree → Nat → Option Forest) (q : Nat)
    (localIH : LocalOrdinaryIH q actual) (T : Option Tree) (ss : List Tree)
    (G : Forest) (ha : agrees T ss G = true) (budget : additionalCost ss G ≤ q) :
    ∃ F, solve actual T ss q = some F ∧ F.length ≤ G.length :=
  (exact_at_budget_bound q actual localIH).2 T ss q G (Nat.le_refl _) ha budget
end GenericForest.LocalIH
