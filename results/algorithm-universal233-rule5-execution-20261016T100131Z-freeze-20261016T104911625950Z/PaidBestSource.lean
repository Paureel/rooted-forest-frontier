import PaidRequestWork
import PaidDomains
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion WholeSourceWork CoreWork GenericForest.CheckCorrespondence GenericForest.FrontierWork
open CherryBranching Rule5Case322 Rule5PaidSelector Case322PaidGuard Rule5SelectedLocalWork Rule5RemainingLocalWork Rule5PendantLocalWork

def originalAcceptedMeter (T S : Tree) (q : Nat) (F : Forest) : Measured Bool :=
 let a:=measuredAgreement T S F;⟨a.value&&decide (F.length-1≤q),a.work+F.length+3⟩
@[simp] theorem original_accepted_value (T S : Tree) (q : Nat) (F : Forest) :
 (originalAcceptedMeter T S q F).value=Rule5PaidOrdinary.originalAccepted T S q F := by
 simp only [originalAcceptedMeter,measuredAgreement_value,Rule5PaidOrdinary.originalAccepted]

def bestForMeter (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} (R : SelectedPaid T S) (q : Nat) : PaidExecutionReceipt (Option Forest) :=
 let a:=answersMeter cb W R q
 let b:=bestLengthMeter (originalAcceptedMeter T S q) a.value
 ⟨b.value,a.prefixWork+b.work+a.value.length+2,a.forestDebit,a.ordinaryCalls⟩
@[simp] theorem best_for_value (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} (R : SelectedPaid T S) (q : Nat) :
 (bestForMeter cb W R q).value=Rule5PaidOrdinary.bestFor cb R q := by
 simp only [bestForMeter,best_length_value,original_accepted_value,answers_value,Rule5PaidOrdinary.bestFor]

theorem best_for_prefix_zero (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} (R : SelectedPaid T S) (q : Nat) :
 (bestForMeter cb W R q).prefixWork=(bestForMeter cb (fun _ _ _=>0) R q).prefixWork := by
 simp only [bestForMeter,answers_prefix_zero,answers_value]

theorem best_for_debit_split (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} (R : SelectedPaid T S) (q : Nat) :
 (bestForMeter cb W R q).forestDebit=(bestForMeter cb (fun _ _ _=>0) R q).forestDebit+
 queryWork W (bestForMeter cb W R q).ordinaryCalls := answers_debit_split cb W R q

def solveSelectedMeter (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) : PaidExecutionReceipt Rule5PaidOrdinary.SelectedResult :=
 let p:=paidSelectedMeter classFee literalFee T S a b
 match p.value with
 | none=>⟨.builderRefused,p.work+2,0,[]⟩
 | some R=>
  let r:=bestForMeter cb W R q
  ⟨.answered r.value,p.work+r.prefixWork+2,r.forestDebit,r.ordinaryCalls⟩
@[simp] theorem solve_selected_value (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) :
 (solveSelectedMeter cb W classFee literalFee T S a b q).value=Rule5PaidOrdinary.solveSelected cb T S a b q := by
 cases hp:Rule5PaidSelector.buildSelected T S a b <;> simp [solveSelectedMeter,paid_selected_value,hp,Rule5PaidOrdinary.solveSelected,best_for_value]

theorem solve_selected_prefix_zero (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) :
 (solveSelectedMeter cb W classFee literalFee T S a b q).prefixWork=
 (solveSelectedMeter cb (fun _ _ _=>0) classFee literalFee T S a b q).prefixWork := by
 cases hp:(paidSelectedMeter classFee literalFee T S a b).value <;>
 simp only [solveSelectedMeter,hp,best_for_prefix_zero]

theorem solve_selected_debit_split (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) :
 (solveSelectedMeter cb W classFee literalFee T S a b q).forestDebit=
 (solveSelectedMeter cb (fun _ _ _=>0) classFee literalFee T S a b q).forestDebit+
 queryWork W (solveSelectedMeter cb W classFee literalFee T S a b q).ordinaryCalls := by
 cases hp:(paidSelectedMeter classFee literalFee T S a b).value with
 | none=>simp [solveSelectedMeter,hp,queryWork]
 | some R=>simpa only [solveSelectedMeter,hp] using best_for_debit_split cb W R q

def paidSelectedSource (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) : Charged Rule5PaidOrdinary.SelectedResult :=
 let r:=solveSelectedMeter cb W classFee literalFee T S a b q;⟨r.value,r.prefixWork+r.forestDebit⟩
@[simp] theorem paid_selected_source_value (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) :
 (paidSelectedSource cb W classFee literalFee T S a b q).value=Rule5PaidOrdinary.solveSelected cb T S a b q:=solve_selected_value _ _ _ _ _ _ _ _ _

theorem paid_selected_source_split (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) :
 (paidSelectedSource cb W classFee literalFee T S a b q).work=
 (paidSelectedSource cb (fun _ _ _=>0) classFee literalFee T S a b q).work+
 queryWork W (solveSelectedMeter cb W classFee literalFee T S a b q).ordinaryCalls := by
 have p:=solve_selected_prefix_zero cb W classFee literalFee T S a b q
 have d:=solve_selected_debit_split cb W classFee literalFee T S a b q
 simp only [paidSelectedSource];omega
end Universal233.Rule5ExecutionSource
