import Rule4SourceBound
namespace OrdinaryDispatch.FullSourceWork
open RMAF Universal233 Universal233.Rule5PendantLocalWork

theorem rule4_minimalBudget_two_explicit (N : Nat) :
 minimalBudget 2 N=384*N^3+32*N^2+8*N := by
 unfold minimalBudget
 grind

theorem rule4_cutGuardBudget_explicit (N : Nat) :
 cutGuardBudget N=768*N^3+72*N^2+26*N+8 := by
 unfold cutGuardBudget
 rw [rule4_minimalBudget_two_explicit]
 grind

theorem rule4_cutsBudget_explicit (N : Nat) :
 cutsBudget N=1536*N^4+144*N^3+116*N^2+20*N+2 := by
 unfold cutsBudget
 rw [rule4_cutGuardBudget_explicit]
 grind

theorem rule4BranchCap_explicit (N : Nat) :
 rule4BranchCap N=1536*N^4+144*N^3+116*N^2+28*N+20 := by
 unfold rule4BranchCap
 rw [rule4_cutsBudget_explicit]
 omega
end OrdinaryDispatch.FullSourceWork
