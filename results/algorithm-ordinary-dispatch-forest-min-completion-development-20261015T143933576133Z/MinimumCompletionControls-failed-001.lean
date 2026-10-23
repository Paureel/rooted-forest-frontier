import ForestMinimumCompletion
import MinPrecontrols
namespace ForestMinCompletion.Controls
open RMAF GenericForest

theorem actual_AF_derives_minimum :
 ∃ M : Forest, agreement cherry cherry M = true ∧ M.length = 1 ∧
   ∀ G, agreement cherry cherry G = true → M.length ≤ G.length := by
 obtain ⟨M,hM,least⟩ := minimum_from_original_AF cherry_split_agrees
 have le := least [[0,1]] cherry_join_agrees
 have ne : M ≠ [] := by
   intro e; rw [e] at hM
   have no : agreement cherry cherry [] = false := by decide
   simp [no] at hM
 refine ⟨M,hM,?_,least⟩
 cases M with
 | nil => exact False.elim (ne rfl)
 | cons B M => simp only [List.length_cons] at le ⊢; omega

def garbage : Tree → Tree → Nat → Option Forest := fun _ _ _ => some []
def absent : Tree → Tree → Nat → Option Forest := fun _ _ _ => none

/-- No properness or local-IH premise is needed for exact low-budget values. -/
theorem improper_boundary_preserved : ghost 0 garbage improper improper 0 = some [] := by
 exact ghost_eq_actual 0 garbage improper improper 0 (by decide)

theorem all_pairs_boundary_preserved (actual : Tree → Tree → Nat → Option Forest) (K : Nat) :
 ∀ t s, ghost K actual t s K = actual t s K := by
 intro t s
 exact ghost_eq_actual K actual t s K (Nat.le_refl K)

theorem feasible_high_ghost : ∃ F : Forest, ghost 0 absent cherry cherry 1 = some F := by
 obtain ⟨F,hF⟩ := minimumCallback_complete (b:=1) cherry_join_agrees (by decide)
 exact ⟨F,by simpa [ghost] using hF⟩

/-- This exposes the intended distinction between proof support and actual
execution: equality is guaranteed only at the prescribed low budgets. -/
theorem high_ghost_can_differ : ghost 0 absent cherry cherry 1 ≠ absent cherry cherry 1 := by
 obtain ⟨F,hF⟩ := feasible_high_ghost
 intro eq
 rw [eq] at hF
 contradiction

theorem local_IH_supplies_global_ghost {K : Nat}
 {actual : Tree → Tree → Nat → Option Forest} (h : LocalOrdinaryIH K actual) :
 OrdinaryIH (ghost K actual) := ghost_global_ordinaryIH h

end ForestMinCompletion.Controls
