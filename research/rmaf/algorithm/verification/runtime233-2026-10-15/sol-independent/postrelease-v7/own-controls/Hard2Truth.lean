import Hard2FullOutputSource
open RMAF Universal233 OrdinaryDispatch.Hard2SourceWork
example : (pairEdgesMeter (.node (.leaf 0) (.leaf 1))).value.length = 2 := by decide +kernel
example : (pairEdgesMeter (.node (.leaf 0) (.leaf 1))).work = 14 := by decide +kernel
example : (pairProperMeter (.leaf 7) [7] [7]).value = false := by decide +kernel
example : (checkedMeter (.leaf 0) (.leaf 0) 0 none).work = 2 := by decide +kernel
example : (chooseMeter (some [[0]]) (some [[1]])).value = some [[0]] := by decide +kernel
example : (chooseMeter (some [[0]]) (some [[1]])).work = 6 := by decide +kernel
example : (fullOutputsSource (fun _ _ _=>none) (fun _ _ _=>0) (.leaf 0) (.leaf 0) 0 [⟨[],[[]]⟩,⟨[],[[]]⟩]).work = 18 := by decide +kernel
