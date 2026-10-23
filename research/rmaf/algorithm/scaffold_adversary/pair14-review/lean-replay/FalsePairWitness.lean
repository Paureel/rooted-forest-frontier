import PairWitness
namespace Universal233.ScaffoldWitness
open RMAF
theorem falseOwnBudget : (0 : Nat) = 2 := by decide
theorem falseCompatible : paidPartitions.all (fun bs => (bs.filter (fun b => !restrictionAgrees originalT originalS b)).length == 0) = true := by decide
end Universal233.ScaffoldWitness
