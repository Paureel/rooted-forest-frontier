import ForestPretestControls
import ForestPretestWork
namespace ForestPretest01.Controls
open RMAF ForestState ForestPretest01

theorem missing_edge_universal_failure :
    ∀ G ∈ omitFirst, ¬ ForestPerm witness G := by
  intro G hG hp
  have hm := hp.members
  have hc : coversWitness G = true := by
    apply List.all_eq_true.2
    intro A hA
    obtain ⟨B,hB,hAB⟩ := hm A hA
    exact List.any_eq_true.2 ⟨B,hB,decide_eq_true hAB⟩
  have bad : coversWitness G = false := by
    have hall : omitFirst.all (fun F => !coversWitness F) = true := by decide
    have hh := List.all_eq_true.1 hall G hG
    simpa using hh
  simp [bad] at hc

example : ∃ G ∈ omitFirst, agrees (some t) ss G = true := by decide
example : ∃ G ∈ candidates ss, ForestPerm witness G ∧ agrees (some t) ss G = true ∧
    additionalCost ss G = 1 := by
  obtain ⟨G,hG,hp,ha,hc⟩ := universal_coverage (some t) ss witness (by decide) (by decide)
  exact ⟨G,hG,hp,ha,hc⟩
end ForestPretest01.Controls
