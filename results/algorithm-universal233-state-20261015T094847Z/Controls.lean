import State
open RMAF ForestState
abbrev T := Tree.node (.node (.leaf 17) (.leaf 31)) (.leaf 47)
abbrev S := Tree.node (.leaf 47) (.node (.leaf 31) (.leaf 17))
abbrev U := Tree.node (.node (.leaf 17) (.leaf 47)) (.leaf 31)
example : cherryReady (some T) [S] 17 31 89 = true := by decide
example : agrees (some T) [S] [[17,31,47]] = true := by decide
example : agrees (some (contract 17 31 89 T)) [contract 17 31 89 S]
  [[89,47]] = true := by decide
example : contractBlock 17 31 89 [47,31,17] = [89,47] := by decide
example : expandBlock 17 31 89 [89,47] = [17,31,47] := by decide
example : agrees (some T) [S] [[17],[31,47]] = true := by decide
example : agrees (some T) [S] [[17,31,47]] = true := by decide
example : agrees (some T) [.leaf 17,.node (.leaf 31) (.leaf 47)] [[17],[31,47]] = true := by decide
example : cleanupTarget (some T) 17 = some (.node (.leaf 31) (.leaf 47)) := by decide
example : agrees (cleanupTarget (some T) 17)
  (cleanupSources [.leaf 17,.node (.leaf 31) (.leaf 47)] 17)
  (cleanupForest [[17],[31,47]] 17) = true := by decide
example : additionalCost [.leaf 17,.node (.leaf 31) (.leaf 47)] [[17],[31,47]] =
  additionalCost (cleanupSources [.leaf 17,.node (.leaf 31) (.leaf 47)] 17)
    (cleanupForest [[17],[31,47]] 17) := by decide
example : cleanupTarget (some (.leaf 17)) 17 = none := by decide
example : agrees none [] [] = true := by decide
example : cherryReady (some T) [S] 17 99 89 = false := by decide
example : cherryReady (some T) [S] 17 17 89 = false := by decide
example : cherryReady (some T) [S] 17 31 47 = false := by decide
example : proper (some (.node (.leaf 17) (.leaf 17))) [.node (.leaf 17) (.leaf 17)] = false := by decide
example : proper (some T) [.leaf 17,S] = false := by decide
example : cherryReady (some T) [U] 17 31 89 = false := by decide
example : cherryReady (some U) [T] 17 31 89 = false := by decide
example : agrees (some T) [U] [[17],[31,47]] = true := by decide
example : agrees (some (contract 17 31 89 T)) [contract 17 31 89 U]
  ([[17],[31,47]].map (contractBlock 17 31 89)) = false := by decide
example : additionalCost [.node (.leaf 17) (.leaf 31),.node (.leaf 47) (.leaf 59)]
  [[17],[31],[47,59]] = 1 := by decide
example : (3 : Nat) - 1 = 2 := by decide
