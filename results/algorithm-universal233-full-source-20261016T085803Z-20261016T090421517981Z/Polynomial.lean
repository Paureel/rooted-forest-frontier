import GuardCost
namespace AllGoodDP.LocalWork
open RMAF ForestState

theorem runPolynomial_monomial (n : Nat) : runPolynomial n≤1048576*(n+1)^4 := by
 unfold runPolynomial guardPolynomial candidatePolynomial solveBill tableCoefficient nodeCharge chooseCap ownerRowCap blocksBill
 grind

theorem actual_run_polynomial (t : Tree) (ss : List Tree) (hp : proper (some t) ss=true) :
 (meterRun (some t) ss).work≤1048576*((leaves t).length+1)^4 :=
 Nat.le_trans (actual_run_work t ss hp) (runPolynomial_monomial _)
end AllGoodDP.LocalWork
