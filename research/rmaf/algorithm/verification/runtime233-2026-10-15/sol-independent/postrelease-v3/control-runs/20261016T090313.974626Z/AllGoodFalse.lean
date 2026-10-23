import Polynomial
open AllGoodDP.LocalWork Universal233.WholeSourceWork
private def fee (n : Nat) : Charged Nat := ⟨if n=0 then 2 else if n=1 then 1 else 3,if n=0 then 5 else if n=1 then 7 else 11⟩
example : (meterBest fee [0,1,2]).work=65 := by decide +kernel
