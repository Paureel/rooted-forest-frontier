import PaidSelectedExecution
import CommonSourceDebit
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence GenericForest.FrontierWork
open CherryBranching Rule5Case322 Rule5PaidSelector Case322PaidGuard Rule5SelectedLocalWork Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5OrdinaryDispatch

/-- All five literal runSelected arms use implemented source counters.
Classifier primitives and LiteralProps retain their distinct named boundaries. -/
def runSelectedSource (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) : FinalSelection→Charged Result
 | .prefix s=>let r:=selectedArmSource cb W T S a b q (.prefix s);⟨.answered r.value,r.work+2⟩
 | .remaining d (.first u v)=>let r:=selectedArmSource cb W T S a b q (.remaining d (.first u v));⟨.answered r.value,r.work+2⟩
 | .remaining d (.third u v)=>let r:=selectedArmSource cb W T S a b q (.remaining d (.third u v));⟨.answered r.value,r.work+2⟩
 | .remaining d (.one _)=>let r:=commonSource cb W T S a b d q;⟨.answered r.value,r.work+2⟩
 | .remaining _ (.second _ _)=>
  let r:=paidSelectedSource cb W classFee literalFee T S a b q
  ⟨match r.value with | .builderRefused=>.paidBuilderRefused | .answered F=>.answered F,r.work+2⟩

@[simp] theorem run_selected_source_value (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) (z : FinalSelection) :
 (runSelectedSource cb W classFee literalFee T S a b q z).value=runSelected cb T S a b q z := by
 cases z with
 | «prefix» s=>exact selectedArmSource_value cb W T S a b q _ trivial
 | remaining d z=>cases z with
  | first u v=>exact selectedArmSource_value cb W T S a b q _ trivial
  | third u v=>exact selectedArmSource_value cb W T S a b q _ trivial
  | one e=>simp only [runSelectedSource,common_source_value,runSelected]
  | second u v=>simp only [runSelectedSource,paid_selected_source_value,runSelected]

def runSelectedCalls (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) : FinalSelection→List Query
 | .prefix s=>(childrenTrace cb T S q (selectedChildrenMeter S a b (.prefix s)).value).queries
 | .remaining d (.first u v)=>(childrenTrace cb T S q (selectedChildrenMeter S a b (.remaining d (.first u v))).value).queries
 | .remaining d (.third u v)=>(childrenTrace cb T S q (selectedChildrenMeter S a b (.remaining d (.third u v))).value).queries
 | .remaining d (.one _)=>Rule5ActualTrace.directQueries (Rule5CommonSelector.commonJobs T S a b d q)
 | .remaining _ (.second _ _)=>(solveSelectedMeter cb W classFee literalFee T S a b q).ordinaryCalls

theorem query_work_direct (W : OrdinaryWork) (js : List OrdinaryCommonSplit.Caller.Job) :
 queryWork W (Rule5ActualTrace.directQueries js)=(js.map (fun j=>W j.T j.S j.budget)).sum := by
 simp only [queryWork,Rule5ActualTrace.directQueries,List.map_map]

theorem run_selected_source_split (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) (z : FinalSelection) :
 (runSelectedSource cb W classFee literalFee T S a b q z).work=
 (runSelectedSource cb (fun _ _ _=>0) classFee literalFee T S a b q z).work+
 queryWork W (runSelectedCalls cb W classFee literalFee T S a b q z) := by
 cases z with
 | «prefix» s=>have h:=selectedArmSource_split cb W T S a b q (.prefix s);simp only [runSelectedSource,runSelectedCalls];omega
 | remaining d z=>cases z with
  | first u v=>have h:=selectedArmSource_split cb W T S a b q (.remaining d (.first u v));simp only [runSelectedSource,runSelectedCalls];omega
  | third u v=>have h:=selectedArmSource_split cb W T S a b q (.remaining d (.third u v));simp only [runSelectedSource,runSelectedCalls];omega
  | one e=>have h:=common_source_split cb W T S a b d q;simp only [runSelectedSource,runSelectedCalls,query_work_direct];omega
  | second u v=>have h:=paid_selected_source_split cb W classFee literalFee T S a b q;simp only [runSelectedSource,runSelectedCalls];omega

/-- Strict outer classifier occurrence followed by its selected source body.
The paid arm's builder separately repeats the classifier as in the source. -/
def dispatchSource (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) : Charged Result :=
 let c:=finalMeter classFee T S a b
 match c.value with
 | none=>⟨.selectorRefused,c.work+2⟩
 | some z=>let r:=runSelectedSource cb W classFee literalFee T S a b q z;⟨r.value,c.work+r.work+2⟩

@[simp] theorem dispatch_source_value (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) :
 (dispatchSource cb W classFee literalFee T S a b q).value=dispatch cb T S a b q := by
 cases hp:selectFinal T S a b <;> simp [dispatchSource,dispatch,final_value,hp]
end Universal233.Rule5ExecutionSource
