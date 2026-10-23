import ClassifierPayload
open RMAF Universal233.Rule5PendantLocalWork
private def r : CheckRequest := .restriction (.leaf 0) (.leaf 0) [0]
example : (andSequence [fun _=>⟨false,5,[r]⟩,fun _=>⟨true,7,[r,r]⟩]).work=18 := by decide +kernel
