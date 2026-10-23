import ERInterface
open OrdinaryDispatch.EarlyLocalWork Universal233.WholeSourceWork
private def f (n : Nat) : Charged Bool := ⟨n==2,if n=0 then 3 else if n=1 then 5 else if n=2 then 7 else 11⟩
example : (meterFind f [0,1,2,3]).work=16 := by decide +kernel
