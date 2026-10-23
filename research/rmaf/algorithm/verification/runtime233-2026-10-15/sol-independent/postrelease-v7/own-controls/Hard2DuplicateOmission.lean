import Hard2FullOutputSource
open RMAF Universal233 OrdinaryDispatch.Hard2SourceWork
example : (fullOutputsSource (fun _ _ _=>none) (fun _ _ _=>0) (.leaf 0) (.leaf 0) 0 [⟨[],[[]]⟩,⟨[],[[]]⟩]).work = 10 := by decide +kernel
