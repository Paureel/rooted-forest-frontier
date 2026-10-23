import ControlFlowV4
import Hard2Program
open RMAF Universal233
namespace FreshOrdinaryBridge
theorem minimum_from_AF (T S : Tree) (G : MafScheduler.Forest)
    (hG : agreement T S G=true) :
    ∃M,agreement T S M=true ∧ ∀H,agreement T S H=true → M.length≤H.length := by
  classical
  have build : ∀n,∀F : MafScheduler.Forest,F.length=n → agreement T S F=true →
      ∃M,agreement T S M=true ∧ ∀H,agreement T S H=true → M.length≤H.length := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro F hlen hF
      by_cases lower : ∃H : MafScheduler.Forest,agreement T S H=true ∧ H.length<n
      · obtain ⟨H,hH,hlt⟩:=lower
        exact ih H.length hlt H rfl hH
      · refine ⟨F,hF,?_⟩
        intro H hH
        have hn : ¬H.length<n := fun hlt=>lower ⟨H,hH,hlt⟩
        omega
  exact build G.length G rfl hG

theorem local_minimum_from_AF (T S : Tree) (G : MafScheduler.Forest)
    (hG : agreement T S G=true) : ∃m,MafScheduler.LocalMinimum T S m := by
  obtain ⟨M,hM,hmin⟩:=minimum_from_AF T S G hG
  exact ⟨M.length-1,⟨M,hM,rfl⟩,fun H hH=>Nat.sub_le_sub_right (hmin H hH) 1⟩
end FreshOrdinaryBridge

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshOrdinaryBridge.minimum_from_AF
#print axioms FreshOrdinaryBridge.minimum_from_AF
#check @FreshOrdinaryBridge.local_minimum_from_AF
#print axioms FreshOrdinaryBridge.local_minimum_from_AF
