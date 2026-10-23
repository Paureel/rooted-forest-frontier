import Rule5QueryDomains
open RMAF Universal233.Rule5ExecutionSource Universal233.Rule5SelectedLocalWork
example : (requestListMeter (.leaf 0) (.leaf 0) 0 [⟨.source,[[]],[]⟩,⟨.source,[[]],[]⟩]).work = 7 := by decide +kernel
