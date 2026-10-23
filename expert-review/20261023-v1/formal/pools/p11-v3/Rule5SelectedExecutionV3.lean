import Rule5PaidSelectionExecutionV3

namespace SourceRule5SelectedV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5ExecutionSource Universal233.Rule5FinalClassification
open Universal233.ClassifierCheckFee Universal233.PaidLiteralDecisionWork
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def armReturn (r : Charged (Option F)) : Charged Rule5OrdinaryDispatch.Result :=⟨.answered r.value,r.work+2⟩
def commonReturn (r : CommonReceipt (Option F)) : Charged Rule5OrdinaryDispatch.Result :=
  ⟨.answered r.value,r.localWork+r.recursiveWork+2⟩
def paidReturn (r : PaidExecutionReceipt Rule5PaidOrdinary.SelectedResult) : Charged Rule5OrdinaryDispatch.Result :=
  ⟨match r.value with | .builderRefused=>.paidBuilderRefused | .answered F=>.answered F,
    r.prefixWork+r.forestDebit+2⟩

inductive SelectedExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (a b q k : Nat) : FinalSelection→Charged Rule5OrdinaryDispatch.Result→List SourceForestV3.S→Prop
  | prefixArm (execution : SourceRule5SelectedArmV3.ArmExec OrdExec mode T S a b q k (.prefix s) r slots) :
      SelectedExec OrdExec mode T S a b q k (.prefix s) (armReturn r) slots
  | firstArm (execution : SourceRule5SelectedArmV3.ArmExec OrdExec mode T S a b q k (.remaining d (.first u v)) r slots) :
      SelectedExec OrdExec mode T S a b q k (.remaining d (.first u v)) (armReturn r) slots
  | thirdArm (execution : SourceRule5SelectedArmV3.ArmExec OrdExec mode T S a b q k (.remaining d (.third u v)) r slots) :
      SelectedExec OrdExec mode T S a b q k (.remaining d (.third u v)) (armReturn r) slots
  | commonArm (execution : SourceRule5CommonV3.CommonExec OrdExec mode T S a b q k d r slots) :
      SelectedExec OrdExec mode T S a b q k (.remaining d (.one x)) (commonReturn r) slots
  | paidArm (execution : SourceRule5PaidSelectionV3.SolvedExec OrdExec mode T S a b q k r slots) :
      SelectedExec OrdExec mode T S a b q k (.remaining d (.second u v)) (paidReturn r) slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem selected_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : SelectedExec OrdExec mode T S a b q k z r slots) :
    r=runSelectedSource (ordinarySpec mode base) (fun _ _ _=>0) checkFee (literalFee T S a b) T S a b q z := by
  cases h with
  | prefixArm execution =>
    have hv:=SourceRule5SelectedArmV3.arm_source_fields sound execution
    simp only [armReturn,runSelectedSource,hv]
  | firstArm execution =>
    have hv:=SourceRule5SelectedArmV3.arm_source_fields sound execution
    simp only [armReturn,runSelectedSource,hv]
  | thirdArm execution =>
    have hv:=SourceRule5SelectedArmV3.arm_source_fields sound execution
    simp only [armReturn,runSelectedSource,hv]
  | commonArm execution =>
    have hv:=SourceRule5CommonV3.common_source_view sound execution
    simp only [SourceRule5CommonV3.sourceView] at hv
    simp only [commonReturn,runSelectedSource,←hv]
  | paidArm execution =>
    have hv:=SourceRule5PaidSelectionV3.solved_source_view sound execution
    simp only [SourceRule5PaidSelectionV3.sourceView] at hv
    simp only [paidReturn,runSelectedSource,←hv]
    rfl

theorem selected_slots_realize (h : SelectedExec OrdExec mode T S a b q k z r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | prefixArm execution => exact SourceRule5SelectedArmV3.arm_slots_realize execution
  | firstArm execution => exact SourceRule5SelectedArmV3.arm_slots_realize execution
  | thirdArm execution => exact SourceRule5SelectedArmV3.arm_slots_realize execution
  | commonArm execution => exact SourceRule5CommonV3.common_slots_realize execution
  | paidArm execution => exact SourceRule5PaidSelectionV3.solved_slots_realize execution

theorem selected_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (a b q k : Nat) (z : FinalSelection) :
    ∃ r slots,SelectedExec OrdExec mode T S a b q k z r slots := by
  cases z with
  | «prefix» s =>
    obtain ⟨r,slots,execution⟩:=SourceRule5SelectedArmV3.arm_exists total T S a b q k (.prefix s)
    exact ⟨_,_,SelectedExec.prefixArm execution⟩
  | remaining d boundary =>
    cases boundary with
    | first u v =>
      obtain ⟨r,slots,execution⟩:=SourceRule5SelectedArmV3.arm_exists total T S a b q k (.remaining d (.first u v))
      exact ⟨_,_,SelectedExec.firstArm execution⟩
    | third u v =>
      obtain ⟨r,slots,execution⟩:=SourceRule5SelectedArmV3.arm_exists total T S a b q k (.remaining d (.third u v))
      exact ⟨_,_,SelectedExec.thirdArm execution⟩
    | one x =>
      obtain ⟨r,slots,execution⟩:=SourceRule5CommonV3.common_exists total T S a b q k d
      exact ⟨_,_,SelectedExec.commonArm execution⟩
    | second u v =>
      obtain ⟨r,slots,execution⟩:=SourceRule5PaidSelectionV3.solved_exists total T S a b q k
      exact ⟨_,_,SelectedExec.paidArm execution⟩
end SourceRule5SelectedV3
