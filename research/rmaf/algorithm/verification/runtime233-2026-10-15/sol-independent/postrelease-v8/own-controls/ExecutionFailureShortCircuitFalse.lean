import Rule5QueryDomains
open RMAF Universal233.Rule5ExecutionSource Universal233.Rule5SelectedLocalWork
example : (jobsAnswersMeter (fun _ _ _=>none) (fun _ _ _=>7) [⟨.leaf 0,.leaf 0,2⟩,⟨.leaf 0,.leaf 0,2⟩]).recursiveWork = 7 := by decide +kernel
