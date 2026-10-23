import Rule5QueryDomains
open RMAF Universal233.Rule5ExecutionSource Universal233.Rule5SelectedLocalWork
example : (jobsAnswersMeter (fun _ _ _=>none) (fun _ _ _=>7) [⟨.leaf 0,.leaf 0,2⟩,⟨.leaf 0,.leaf 0,2⟩]).recursiveWork = 14 := by decide +kernel
example : (jobsAnswersMeter (fun _ _ _=>none) (fun _ _ _=>7) [⟨.leaf 0,.leaf 0,2⟩,⟨.leaf 0,.leaf 0,2⟩]).localWork = 7 := by decide +kernel
example : (jobsAnswersMeter (fun _ _ _=>none) (fun _ _ _=>7) [⟨.leaf 0,.leaf 0,2⟩,⟨.leaf 0,.leaf 0,2⟩]).calls.length = 2 := by decide +kernel
example : (bestAdditionalMeter [.leaf 0,.leaf 1,.leaf 2] (fun _=>⟨true,1⟩) [[[0],[1]],[[0]]]).value = some [[0],[1]] := by decide +kernel
example : (bestAdditionalMeter [.leaf 0,.leaf 1,.leaf 2] (fun _=>⟨true,1⟩) [[[0],[1]],[[0]]]).work = 26 := by decide +kernel
example : (bestLengthMeter (fun _=>⟨true,1⟩) [[[0],[1]],[[0]]]).value = some [[0]] := by decide +kernel
example : (requestListMeter (.leaf 0) (.leaf 0) 0 [⟨.source,[[]],[]⟩,⟨.source,[[]],[]⟩]).value.length = 0 := by decide +kernel
example : (requestListMeter (.leaf 0) (.leaf 0) 0 [⟨.source,[[]],[]⟩,⟨.source,[[]],[]⟩]).work = 13 := by decide +kernel
example : (currentQueryMeter (fun _ _ _=>none) (fun _ _ _=>7) (some (.leaf 0)) [] 5).forestDebit = 0 := by decide +kernel
example : (currentQueryMeter (fun _ _ _=>none) (fun _ _ _=>7) none [] 0).ordinaryCalls.length = 0 := by decide +kernel
