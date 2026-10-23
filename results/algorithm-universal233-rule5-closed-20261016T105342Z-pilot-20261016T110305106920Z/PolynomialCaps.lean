import ConcreteFees
namespace Universal233.Rule5ClosedSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5SelectedLocalWork
open ClassifierCheckFee PaidLiteralDecisionWork

/-- Structural monotonicity for the positive Nat polynomial source caps.
It creates ordinary checked inequalities, without a numeric fit or oracle. -/
macro "poly_mono" : tactic => `(tactic|repeat first
 | assumption
 | exact Nat.le_refl _
 | apply Nat.add_le_add
 | apply Nat.mul_le_mul
 | omega)

theorem check_cap_mono {n N : Nat} (h:n≤N) : checkCap n≤checkCap N := by
 simp only [checkCap,requestSize,payloadCap]
 (try simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one])
 poly_mono

theorem literal_budget_mono {n N : Nat} (h:n≤N) : literalBudget n≤literalBudget N := by
 rw [literal_budget_expanded,literal_budget_expanded]
 (try simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one])
 poly_mono

theorem agreement_K_mono {n N : Nat} (h:n≤N) : agreementK n≤agreementK N := by
 unfold agreementK
 (try simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one])
 poly_mono

theorem final_budget_mono {nt ns K N M H : Nat} (tn:nt≤N) (sn:ns≤M) (kh:K≤H) :
 finalBudget nt ns K≤finalBudget N M H := by
 simp only [Universal233.Rule5PendantLocalWork.finalBudget,Universal233.Rule5PendantLocalWork.localBudget,Universal233.Rule5PendantLocalWork.admittedBudget,Universal233.Rule5PendantLocalWork.partitionBudget,Universal233.Rule5PendantLocalWork.cutsBudget,Universal233.Rule5PendantLocalWork.cutGuardBudget,Universal233.Rule5PendantLocalWork.minimalBudget,Universal233.Rule5PendantLocalWork.blocksBudget,Universal233.Rule5PendantLocalWork.coreBudget,Universal233.Rule5PendantLocalWork.pendantPayloadBudget,Universal233.Rule5PendantLocalWork.payloadCap,Universal233.Rule5PendantLocalWork.admittedGuardBudget,Universal233.Rule5PrefixLocalWork.properPolynomial,Universal233.Rule5PendantLocalWork.earlierBudget,Universal233.Rule5PendantLocalWork.candidatesBudget,Universal233.Rule5PendantLocalWork.admittedRule4Budget,Universal233.Rule5PendantLocalWork.rule4CandidateBudget,Universal233.Rule5PendantLocalWork.rule4ArcBudget,Universal233.Rule5PendantLocalWork.localTailBudget,Universal233.Rule5PendantLocalWork.selectLargeBudget,Universal233.Rule5PendantLocalWork.largeAtBudget,Universal233.Rule5PendantLocalWork.selectSizeTwoBudget,Universal233.Rule5PendantLocalWork.sizeTwoAtBudget,Universal233.Rule5PendantLocalWork.selectOutsideBudget,Universal233.Rule5PendantLocalWork.outsideAtBudget,Universal233.Rule5PendantLocalWork.outsideGuardBudget,Universal233.Rule5PendantLocalWork.badCandidatesBudget,Universal233.Rule5PendantLocalWork.badRowBudget,Universal233.Rule5PendantLocalWork.badAtBudget,Universal233.Rule5PendantLocalWork.boundaryBudget,Universal233.Rule5PendantLocalWork.incidentBudget,Universal233.Rule5PendantLocalWork.incidentAtBudget,Universal233.Rule5PendantLocalWork.outsideCheckBudget,Universal233.Rule5PendantLocalWork.paintBudget]
 (try simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one])
 poly_mono

theorem forest_arm_budget_mono {nt ns K N M H : Nat} (tn:nt≤N) (sn:ns≤M) (kh:K≤H) :
 forestArmBudget nt ns K≤forestArmBudget N M H := by
 simp only [Universal233.Rule5SelectedLocalWork.forestArmBudget,Universal233.Rule5SelectedLocalWork.selectedChildrenBudget,Universal233.Rule5SelectedLocalWork.fiveChildrenBudget,Universal233.Rule5SelectedLocalWork.pendantChildBudget,Universal233.Rule5PendantLocalWork.partitionBudget,Universal233.Rule5PendantLocalWork.cutsBudget,Universal233.Rule5PendantLocalWork.cutGuardBudget,Universal233.Rule5PendantLocalWork.minimalBudget,Universal233.Rule5PendantLocalWork.blocksBudget,Universal233.Rule5PendantLocalWork.coreBudget,Universal233.Rule5PendantLocalWork.pendantPayloadBudget,Universal233.Rule5PendantLocalWork.payloadCap,Universal233.Rule5SelectedLocalWork.pairChildBudget,Universal233.Rule5SelectedLocalWork.pairPartitionBudget,Universal233.Rule5SelectedLocalWork.siblingChildrenBudget,Universal233.Rule5SelectedLocalWork.singletonChildBudget,Universal233.Rule5SelectedLocalWork.singletonPartitionBudget]
 (try simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one])
 poly_mono

theorem common_budget_cap {nt ns x N : Nat} (tn:nt≤N) (sn:ns≤N) (xl:x≤2*N) :
 commonBudget nt ns x≤commonBudget N N (2*N) := by
 simp only [Universal233.Rule5ExecutionSource.commonBudget,Universal233.Rule5RemainingLocalWork.commonSetupBudget,Universal233.Rule5PendantLocalWork.coreBudget,Universal233.Rule5PendantLocalWork.pendantPayloadBudget,Universal233.Rule5PendantLocalWork.cutsBudget,Universal233.Rule5PendantLocalWork.cutGuardBudget,Universal233.Rule5PendantLocalWork.minimalBudget,Universal233.Rule5PendantLocalWork.blocksBudget,Universal233.Rule5PendantLocalWork.payloadCap,Universal233.Rule5RemainingLocalWork.setupBudget,GenericForest.CheckCorrespondence.partitionCap,Universal233.Rule5PendantLocalWork.incidentBudget,Universal233.Rule5PendantLocalWork.incidentAtBudget,Universal233.Rule5ExecutionSource.guardedBudget,Universal233.Rule5ExecutionSource.outsideBudget,Universal233.Rule5ExecutionSource.paidBudget,Universal233.Rule5LocalWork.commonPolynomial,agreementK]
 (try simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one])
 poly_mono

theorem paid_selected_budget_mono {nt ns Kc Kl N M Hc Hl : Nat}
 (tn:nt≤N) (sn:ns≤M) (kc:Kc≤Hc) (kl:Kl≤Hl) :
 paidSelectedBudget nt ns Kc Kl≤paidSelectedBudget N M Hc Hl := by
 have f:=final_budget_mono tn sn kc
 simp only [paidSelectedBudget,Universal233.Rule5RemainingLocalWork.secondBuilderBudget,Universal233.Rule5RemainingLocalWork.rowsBudget,Universal233.Rule5RemainingLocalWork.oneBudget,Universal233.Rule5RemainingLocalWork.leafAddressBudget]
 (try simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one])
 poly_mono
end Universal233.Rule5ClosedSource
