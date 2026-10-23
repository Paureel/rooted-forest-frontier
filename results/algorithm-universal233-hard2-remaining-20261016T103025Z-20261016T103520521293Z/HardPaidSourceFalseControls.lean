import HardPaidSourceControls
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.Hard2SourceWork.RemainingControls
example : (kindOutputsMeter (.clique []) one one [7] [] 0).value.length=2 := by decide
example : (generatedOutputsMeter one (color 7) 0).work=(generatedOutputsMeter one (color 0) 0).work := by decide
example : (appendOutputsMeter ⟨[uncut,uncut],10⟩ ⟨[uncut],20⟩).work=34 := by decide
