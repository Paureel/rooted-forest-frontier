import StateExpand
import GraphControls
open RMAF ForestState

-- Different target/source cherry addresses and swapped children, budget zero.
theorem completion_consumer_1 : feasible (some LeftCherry) [RightCherry] 0 ↔
    feasible (some (contract 17 31 89 LeftCherry)) [contract 17 31 89 RightCherry] 0 := by
  exact common_cherry_decision_equivalence LeftCherry [RightCherry] 17 31 89 0 (by decide)

-- An actual current source forest with another component, all budgets.
theorem completion_consumer_2 (q : Nat) :
    feasible (some LeftCherry) [RootCherry,.node (.leaf 47) (.leaf 59)] q ↔
    feasible (some (contract 17 31 89 LeftCherry))
      ([RootCherry,.node (.leaf 47) (.leaf 59)].map (contract 17 31 89)) q := by
  exact common_cherry_state_decision_equivalence _ _ 17 31 89 q (by decide)

theorem completion_consumer_3 :
    ∃ G, agrees (some LeftCherry) [RightCherry] G = true ∧
      G.length ≤ ([[17],[31,47],[59]] : List (List Nat)).length ∧
      ∃ B ∈ G, 17 ∈ B ∧ 31 ∈ B := by
  exact common_cherry_no_larger LeftCherry [RightCherry] [[17],[31,47],[59]] 17 31
    (by decide) (by decide) ⟨RightCherry,by simp,by decide⟩

theorem completion_consumer_4 :
    disjointVertices (minimalVertices [31,17,47] LeftCherry) (minimalVertices [59] LeftCherry) = true := by
  exact endpoint_reassignment_embeddings LeftCherry [17,47] [59] 17 31
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem completion_consumer_5 :
    agrees (some LeftCherry) [RightCherry] ([[89,47],[59]].map (expandBlock 17 31 89)) = true := by
  exact common_cherry_expand_agreement LeftCherry [RightCherry] [[89,47],[59]] 17 31 89
    (by decide) (by decide)

theorem completion_consumer_6 :
    (labels ((some LeftCherry).map (contract 17 31 89))).length + 1 = (labels (some LeftCherry)).length := by
  exact common_cherry_state_strict_decrease _ [RightCherry] 17 31 89 (by decide)

theorem completion_consumer_7 :
    additionalCost [RootCherry,.node (.leaf 47) (.leaf 59)]
      ([[89],[47,59]].map (expandBlock 17 31 89)) =
      additionalCost ([RootCherry,.node (.leaf 47) (.leaf 59)].map (contract 17 31 89)) [[89],[47,59]] := by
  exact common_cherry_expand_exact_cost _ _ _ _ _

-- Root cherry and original singleton blocks exercise the no-larger preparation.
theorem completion_consumer_8 (q : Nat) : feasible (some RootCherry) [RootCherry] q ↔
    feasible (some (contract 17 31 89 RootCherry)) [contract 17 31 89 RootCherry] q := by
  exact common_cherry_decision_equivalence _ _ 17 31 89 q (by decide)
