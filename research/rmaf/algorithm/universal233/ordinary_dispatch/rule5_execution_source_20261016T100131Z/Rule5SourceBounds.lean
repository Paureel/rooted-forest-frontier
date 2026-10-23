import Rule5SelectedSource
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence GenericForest.FrontierWork
open CherryBranching Rule5Case322 Rule5PaidSelector Case322PaidGuard Rule5SelectedLocalWork Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5OrdinaryDispatch Rule5Local

def selectedPrefixBudget (T S : Tree) (Kc Kl : Nat) : FinalSelection→Nat
 | .remaining d (.one _)=>commonBudget (leaves T).length (leaves S).length (subtreeLabels S d.badArc).length+2
 | .remaining _ (.second _ _)=>paidExecutionPrefixBudget T S Kc Kl+2
 | _=>forestArmBudget (leaves T).length (leaves S).length (agreementK (leaves T).length)+2

/-- Implemented GenericForest local work, not an unresolved arm fee. The
common arm directly calls ordinary children, whose zero counter is zero. -/
def selectedForestDebit (cb : Ordinary) (classFee : CheckRequest→Nat) (literalFee : LiteralCall→Nat)
 (T S : Tree) (a b q : Nat) : FinalSelection→Nat
 | .remaining _ (.second _ _)=>(solveSelectedMeter cb (fun _ _ _=>0) classFee literalFee T S a b q).forestDebit
 | .remaining _ (.one _)=>0
 | z=>childForestDebit cb (fun _ _ _=>0) T q (selectedChildrenMeter S a b z).value

theorem run_selected_local_bound (cb : Ordinary) (classFee : CheckRequest→Nat) (literalFee : LiteralCall→Nat)
 {T S : Tree} {i : RMAF.Vertex} {a b : Nat} (ch:CherryAt T i a b) (ad:admitted T S a b=true)
 (hp:DepthOne.proper T S=true) (q L Kc Kl : Nat) {z : FinalSelection}
 (sel:(finalMeter classFee T S a b).value=some z)
 (tlabs : ∀x,x∈leaves T→x<2^L) (slabs : ∀x,x∈leaves S→x<2^L)
 (classifier : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r→classFee r≤Kc)
 (literal : ∀d u v,(finalMeter classFee T S a b).value=some (.remaining d (.second u v))→
  ∀j,LiteralCallDomain T S a b d u v j→literalFee j≤Kl)
 (same : ∀d e,(finalMeter classFee T S a b).value=some (.remaining d (.one e))→
  ∀j,j∈Rule5CommonSelector.commonJobs T S a b d q→cb j.T j.S j.budget=Rule5LocalWork.actual j.T j.S j.budget) :
 (runSelectedSource cb (fun _ _ _=>0) classFee literalFee T S a b q z).work≤
 selectedPrefixBudget T S Kc Kl z+selectedForestDebit cb classFee literalFee T S a b q z := by
 cases z with
 | «prefix» s=>
  have h:=selectedArmSource_local cb classFee T S a b q hp sel
  simp only [runSelectedSource,selectedPrefixBudget,selectedForestDebit];omega
 | remaining d z=>cases z with
  | first u v=>
   have h:=selectedArmSource_local cb classFee T S a b q hp sel
   simp only [runSelectedSource,selectedPrefixBudget,selectedForestDebit];omega
  | third u v=>
   have h:=selectedArmSource_local cb classFee T S a b q hp sel
   simp only [runSelectedSource,selectedPrefixBudget,selectedForestDebit];omega
  | one e=>
   have h:=common_source_local cb classFee ch ad sel q (same d e sel)
   simp only [runSelectedSource,selectedPrefixBudget,selectedForestDebit];omega
  | second u v=>
   have h:=solve_selected_prefix_work cb (fun _ _ _=>0) classFee literalFee T S a b q L Kc Kl tlabs slabs classifier literal
   simp only [runSelectedSource,selectedPrefixBudget,selectedForestDebit,paidSelectedSource];omega

def dispatchCalls (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) : List Query :=
 match (finalMeter classFee T S a b).value with
 | none=>[]
 | some z=>runSelectedCalls cb W classFee literalFee T S a b q z

theorem dispatch_source_split (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) :
 (dispatchSource cb W classFee literalFee T S a b q).work=
 (dispatchSource cb (fun _ _ _=>0) classFee literalFee T S a b q).work+
 queryWork W (dispatchCalls cb W classFee literalFee T S a b q) := by
 cases hc:(finalMeter classFee T S a b).value with
 | none=>simp [dispatchSource,dispatchCalls,hc,queryWork]
 | some z=>
  have h:=run_selected_source_split cb W classFee literalFee T S a b q z
  simp only [dispatchSource,dispatchCalls,hc];omega
end Universal233.Rule5ExecutionSource
