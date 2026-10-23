import ControlFlowV4
import Hard2Program
open RMAF Universal233
namespace FreshOrdinaryBridge
theorem allocated_le {P A : Type} (b : Nat) (js : List (PaidQueries.Job P A)) :
    PaidQueries.allocated b js ≤ b := by
  unfold PaidQueries.allocated
  omega

theorem allocated_strict_of_fee {P A : Type} (outer b fee : Nat)
    (js : List (PaidQueries.Job P A)) (hpay : b+fee≤outer) (hfee : 0<fee) :
    PaidQueries.allocated b js<outer := by
  have := allocated_le b js
  omega

theorem literal_parent_budget_strict {P A : Type} (outer : Nat)
    (Q : List (List Nat)) (js : List (PaidQueries.Job P A))
    (hpay : Q.length-1≤outer) (hparents : 2≤Q.length) :
    PaidQueries.allocated (outer-(Q.length-1)) js<outer := by
  apply allocated_strict_of_fee outer (outer-(Q.length-1)) (Q.length-1) js <;> omega

theorem literal_parent_accounting (outer : Nat) (Q : List (List Nat))
    (hpay : Q.length-1≤outer) :
    (outer-(Q.length-1))+(Q.length-1)=outer := by omega

theorem proper_block_labels (T S : Tree) (U : List Nat)
    (h : MafScheduler.properBlock T S U=true) :
    U.Nodup ∧ U≠[] ∧ ∀ x∈U, x∈leaves T ∧ x∈leaves S := by
  simp only [MafScheduler.properBlock, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    ] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro x hx
  simpa using h.2 x hx

theorem no_prepare_refuses (solve : BothBad.ForestSolver) (T S : Tree)
    (Q : List (List Nat)) (b : Nat) (h : MafScheduler.prepare T S Q=none) :
    (BothBad.ordinaryExecution solve T S Q b).answer=none ∧
    (BothBad.ordinaryExecution solve T S Q b).calls=[] := by
  simp only [BothBad.ordinaryExecution,h]
  exact ⟨True.intro,True.intro⟩

theorem early_schedule_refuses (solve : BothBad.ForestSolver) (T S : Tree)
    (Q : List (List Nat)) (b : Nat) (js : List (PaidQueries.Job (List Nat) MafScheduler.Forest))
    (h : MafScheduler.prepare T S Q=some js)
    (hbudget : b<PaidQueries.knownCost js+2*PaidQueries.pending js) :
    (BothBad.ordinaryExecution solve T S Q b).answer=none ∧
    (BothBad.ordinaryExecution solve T S Q b).calls=[] := by
  have he : BothBad.ordinaryExecution solve T S Q b=BothBad.Execution.mk none [] := by
    unfold BothBad.ordinaryExecution
    rw [h]
    change BothBad.Execution.mk _ _=BothBad.Execution.mk none []
    unfold PaidQueries.meterSchedule
    rw [if_pos hbudget]
    rfl
  rw [he]
  exact ⟨rfl,rfl⟩
end FreshOrdinaryBridge

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshOrdinaryBridge.allocated_le
#print axioms FreshOrdinaryBridge.allocated_le
#check @FreshOrdinaryBridge.allocated_strict_of_fee
#print axioms FreshOrdinaryBridge.allocated_strict_of_fee
#check @FreshOrdinaryBridge.literal_parent_budget_strict
#print axioms FreshOrdinaryBridge.literal_parent_budget_strict
#check @FreshOrdinaryBridge.literal_parent_accounting
#print axioms FreshOrdinaryBridge.literal_parent_accounting
#check @FreshOrdinaryBridge.proper_block_labels
#print axioms FreshOrdinaryBridge.proper_block_labels
#check @FreshOrdinaryBridge.no_prepare_refuses
#print axioms FreshOrdinaryBridge.no_prepare_refuses
#check @FreshOrdinaryBridge.early_schedule_refuses
#print axioms FreshOrdinaryBridge.early_schedule_refuses
