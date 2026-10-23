import CherryTopology
import Controls
open RMAF ForestState

theorem state_consumer_1 : feasible (some T) [.leaf 17,.node (.leaf 31) (.leaf 47)] 0 ↔
    feasible (cleanupTarget (some T) 17)
      (cleanupSources [.leaf 17,.node (.leaf 31) (.leaf 47)] 17) 0 := by
  apply singleton_decision_equivalence
  · decide
  · simp

theorem state_consumer_2 : feasible (some (.leaf 17)) [.leaf 17] 0 ↔ feasible none [] 0 := by
  exact singleton_decision_equivalence (some (.leaf 17)) [.leaf 17] 17 0 (by decide) (by simp)

theorem state_consumer_3 : agrees (some T) [.leaf 17,.node (.leaf 31) (.leaf 47)] [[17],[31,47]] = true ∧
    agrees (cleanupTarget (some T) 17)
      (cleanupSources [.leaf 17,.node (.leaf 31) (.leaf 47)] 17)
      (cleanupForest [[17],[31,47]] 17) = true := by
  have h : agrees (some T) [.leaf 17,.node (.leaf 31) (.leaf 47)] [[17],[31,47]] = true := by decide
  exact ⟨h,singleton_cleanup_forward _ _ _ _ h (by simp)⟩

theorem state_consumer_4 : restrictionAgrees T S [31,17,47] = true := by
  exact synchronized_endpoint_reassignment_topology T S 17 31 [17,47]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem state_consumer_5 : [17] = [17] ∨ [31,47] = [31] := by
  exact actual_separated_cherry_singleton T [S] [[17],[31,47]] 17 31
    (by decide) (by decide) [17] [31,47] (by simp) (by simp)
    (by simp) (by simp) (by decide) (by decide)

theorem state_consumer_6 : (labels (cleanupTarget (some T) 17)).length + 1 = (labels (some T)).length := by
  exact singleton_strict_decrease (some T) [.leaf 17,.node (.leaf 31) (.leaf 47)]
    [[17],[31,47]] 17 (by decide) (by simp)

theorem state_consumer_7 : agrees (some (.node (.node (.leaf 17) (.leaf 31)) (.node (.leaf 47) (.leaf 59))))
    [.node (.leaf 17) (.leaf 31),.node (.leaf 47) (.leaf 59)] [[17],[31],[47,59]] = true := by decide
