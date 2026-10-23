import ExtendedControls
open RMAF Universal233 CoreProgram Hard2Overlap Hard2PaidLocal
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.ExtendedSourceAssembly.Controls
example : caseMass 2 (.four .abc [] [])=1/8 := by
 rw [mass_literals_at_two.2.2.1]
 apply Rat.eq_iff_mul_eq_mul.2
 have n4 : (1/4:Rat).num=1 := by decide +kernel
 have d4 : (1/4:Rat).den=4 := by decide +kernel
 have n8 : (1/8:Rat).num=1 := by decide +kernel
 have d8 : (1/8:Rat).den=8 := by decide +kernel
 rw [n4,d4,n8,d8]
 decide +kernel
example : (hardPaidSource noAnswer (fun _ _ _=>7) (.leaf 0) (.leaf 0) 9 emptyCuts (.clique [])).work=12 := by decide +kernel
example : (fullOutputsSource noAnswer (fun _ _ _=>7) (.leaf 0) (.leaf 0) 0 [unaffordable,unaffordable]).work=10 := by decide +kernel
