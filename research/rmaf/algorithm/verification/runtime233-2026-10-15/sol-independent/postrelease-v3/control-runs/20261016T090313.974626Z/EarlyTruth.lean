import ERInterface
open RMAF OrdinaryDispatch.EarlyLocalWork Universal233.WholeSourceWork
set_option maxRecDepth 100000
namespace OwnPhase3
private def work (n : Nat) := if n=0 then 3 else if n=1 then 5 else if n=2 then 7 else 11
private def found (n : Nat) : Charged Bool := ⟨n==2,work n⟩
private def refused (n : Nat) : Charged Bool := ⟨false,work n⟩
private def valid (n : Nat) : Charged Bool := ⟨true,work n⟩
private def cost (n : Nat) := if n=1 then 0 else 1
example : (meterFind found [0,1,2,3]).value=some 2 ∧ (meterFind found [0,1,2,3]).work=27 := by decide +kernel
example : (meterFind refused [0,1,2,3]).value=none ∧ (meterFind refused [0,1,2,3]).work=43 := by decide +kernel
example : (meterBest cost valid [0,1,2,3]).value=some 1 ∧ (meterBest cost valid [0,1,2,3]).work=63 ∧ (meterBest cost valid [0,1,2,3]).tailSizes=[3,2,1,0] := by decide +kernel
example : ScalarDomain (.leaf 0) (.leaf 0) 1000 1 1000 ∧ ¬1000≤(leaves (.leaf 0)).length := by
 constructor
 · simp [ScalarDomain,leaves]
 · decide +kernel
end OwnPhase3
