import LiteralBounds
namespace Universal233.PaidLiteralDecisionWork
open Rule5PrefixLocalWork Rule5PendantLocalWork

/-- Fully expanded polynomial: the degree-five term pays repeated incident scans. -/
theorem literal_budget_expanded (N : Nat) :
 literalBudget N=1024*N*N*N*N*N+3072*N*N*N*N+960*N*N*N+640*N*N+238*N+164 := by
 simp only [literalBudget,properPolynomial,cherryBudget,cutsBudget,cutGuardBudget,labelsBudget,
  labelPointBudget,membershipBudget,incidentEqBudget,incidentBudget,incidentAtBudget,minimalBudget,
  tailMemBudget,minMemBudget,boundaryBudget,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,
  Nat.mul_assoc,Nat.reduceMul,Nat.reduceAdd]
 simp only [Nat.mul_left_comm N 2,Nat.mul_left_comm N 4,Nat.mul_left_comm N 8,
  Nat.mul_left_comm N 16,Nat.mul_left_comm N 64,Nat.mul_left_comm N 192]
 omega
end Universal233.PaidLiteralDecisionWork
