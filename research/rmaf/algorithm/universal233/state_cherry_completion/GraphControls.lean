import CherryTopology
open RMAF ForestState

abbrev RootCherry := Tree.node (.leaf 17) (.leaf 31)
abbrev LeftCherry := Tree.node RootCherry (.node (.leaf 47) (.leaf 59))
abbrev RightCherry := Tree.node (.node (.leaf 59) (.leaf 47)) (.node (.leaf 31) (.leaf 17))

example : (leaves RootCherry).Nodup := by decide
example : cherry 17 31 RootCherry = true := by decide
example : disjointVertices (minimalVertices [17] RootCherry) (minimalVertices [47] RootCherry) = true := by decide
example : disjointVertices (minimalVertices [31,17] RootCherry) (minimalVertices [47] RootCherry) = true := by decide
example : disjointVertices (minimalVertices [17,47] LeftCherry) (minimalVertices [59] LeftCherry) = true := by decide
example : disjointVertices (minimalVertices [31,17,47] LeftCherry) (minimalVertices [59] LeftCherry) = true := by decide
example : disjointVertices (minimalVertices [31,47] RightCherry) (minimalVertices [59] RightCherry) = true := by decide
example : disjointVertices (minimalVertices [17,31,47] RightCherry) (minimalVertices [59] RightCherry) = true := by decide
example : disjointVertices (minimalVertices [17] RootCherry) (minimalVertices [31] RootCherry) = true := by decide
example : disjointVertices (minimalVertices [31,17] RootCherry) (minimalVertices [31] RootCherry) = false := by decide
example : cherryReady (some LeftCherry) [RightCherry] 17 31 89 = true := by decide
example : cherryReady (some LeftCherry) [RightCherry] 17 31 47 = false := by decide
example : proper (some (.node (.leaf 17) (.leaf 17))) [.node (.leaf 17) (.leaf 17)] = false := by decide
example : agrees (some LeftCherry) [RightCherry] [[17],[31,47],[59]] = true := by decide
example : agrees (some LeftCherry) [RightCherry] [[17,31,47],[59]] = true := by decide
example : agrees (some LeftCherry) [RightCherry] [[17,31],[47],[59]] = true := by decide
example : agrees (some (Tree.node RootCherry (.node (.leaf 47) (.leaf 59))))
  [RootCherry,.node (.leaf 47) (.leaf 59)] [[17],[31],[47,59]] = true := by decide
example : additionalCost [RootCherry,.node (.leaf 47) (.leaf 59)] [[17],[31],[47,59]] = 1 := by decide
example : (3 : Nat) - 1 = 2 := by decide
