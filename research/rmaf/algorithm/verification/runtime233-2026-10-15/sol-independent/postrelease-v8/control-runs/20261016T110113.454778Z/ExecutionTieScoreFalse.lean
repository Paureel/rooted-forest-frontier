import Rule5QueryDomains
open RMAF Universal233.Rule5ExecutionSource Universal233.Rule5SelectedLocalWork
example : (bestAdditionalMeter [.leaf 0,.leaf 1,.leaf 2] (fun _=>⟨true,1⟩) [[[0],[1]],[[0]]]).value = some [[0]] := by decide +kernel
