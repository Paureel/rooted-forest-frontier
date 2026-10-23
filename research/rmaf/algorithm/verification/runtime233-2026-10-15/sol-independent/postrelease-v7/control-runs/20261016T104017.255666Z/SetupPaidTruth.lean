import CommonSetupBinding
import PaidDomains
open Universal233.Rule5RemainingLocalWork Universal233.Rule5PrefixLocalWork
example : (maxMeter [2,7,4]).value = 7 := by decide +kernel
example : (maxMeter [2,7,4]).work = 10 := by decide +kernel
example : 2*(maxMeter [2,7,4]).work = 20 := by decide +kernel
example : (findBuilderMeter (fun x : Nat=>⟨if x=1 then some 99 else none,if x=1 then 7 else 11⟩) [1,2]).work = 9 := by decide +kernel
example : (findBuilderMeter (fun x : Nat=>⟨if x=1 then some 99 else none,if x=1 then 7 else 11⟩) [2,1]).work = 22 := by decide +kernel
