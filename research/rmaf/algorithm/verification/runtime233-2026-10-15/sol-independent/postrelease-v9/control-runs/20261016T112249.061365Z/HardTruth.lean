import HardPaidSourceBound
open RMAF Universal233 Universal233.CoreProgram Universal233.WholeSourceWork OrdinaryDispatch.Hard2SourceWork
private def o : Output := ⟨[[7]],[[false]]⟩
example : (appendOutputsMeter ⟨[o,o],5⟩ ⟨[o],7⟩).work=20 := by decide +kernel
example : (appendOutputsMeter ⟨[o,o],5⟩ ⟨[o],7⟩).value.length=3 := by decide +kernel
example : (fullOutputsSource (fun _ _ _=>none) (fun _ _ _=>7) (.leaf 7) (.leaf 7) 0 [o,o]).work=18 := by decide +kernel
example : (caseOutputsMeter (.leaf 7) (.leaf 7) [] [] [] 0 .disjoint).work=2 := by decide +kernel
example : (([1,2,2,5]:List Nat).map (fun d=>if d≤3 then 2^(3-d) else 0)).sum=8 := by decide +kernel
