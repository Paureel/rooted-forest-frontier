import Controls
open RMAF ForestState
example : cherryReady (some T) [S] 17 31 47 = true := by decide
example : agrees (some (contract 17 31 89 T)) [contract 17 31 89 U]
  ([[17],[31,47]].map (contractBlock 17 31 89)) = true := by decide
example : [17] ∈ ([[17,31,47]] : List (List Nat)) := by decide
example : additionalCost [.node (.leaf 17) (.leaf 31),.node (.leaf 47) (.leaf 59)]
  [[17],[31],[47,59]] = 3 - 1 := by decide
