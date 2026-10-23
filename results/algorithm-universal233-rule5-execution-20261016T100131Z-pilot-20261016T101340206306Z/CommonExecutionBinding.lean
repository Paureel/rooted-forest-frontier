import CommonGuardedSource
import OrdinaryBinding
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph Rule5PrefixLocalWork
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5CommonSelector

def sourceMeter (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (q : Nat) : CommonReceipt (Option (Option Forest)) :=
 let setup:=setupMeter T S X Y p
 match setup.value with
 | none=>⟨none,setup.work+2,0,[]⟩
 | some d=>let r:=guardedMeter cb W d q
            ⟨r.value,setup.work+r.localWork+2,r.recursiveWork,r.calls⟩

theorem source_value (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (q : Nat) :
 (sourceMeter cb W T S X Y p q).value=runSource T S X Y p q cb := by
 simp only [sourceMeter,setup_value,guarded_value,runSource]
 split <;> simp_all

theorem source_calls (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (q : Nat) :
 (sourceMeter cb W T S X Y p q).calls=sourceJobs T S X Y p q := by
 simp only [sourceMeter,setup_value,guarded_calls,sourceJobs]
 split <;> simp_all

theorem source_recursive (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (q : Nat) :
 (sourceMeter cb W T S X Y p q).recursiveWork=
 (((sourceMeter cb W T S X Y p q).calls).map (fun j=>W j.T j.S j.budget)).sum := by
 simp only [sourceMeter]
 split
 · rfl
 · exact guarded_recursive _ _ _ _

/-- Complete common-one execution at the literally recomputed X,Y/setup.
The outer Option is joined only after the guarded source returns. -/
def commonMeter (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) : CommonReceipt (Option Forest) :=
 let setup:=commonSetupMeter T S a b d
 match setup.value with
 | none=>⟨none,setup.work+2,0,[]⟩
 | some built=>let r:=guardedMeter cb W built q
                ⟨r.value.join,setup.work+r.localWork+3,r.recursiveWork,r.calls⟩

theorem common_value (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) :
 (commonMeter cb W T S a b d q).value=Rule5CommonOrdinary.runSelectedCommon cb T S a b d q := by
 simp only [commonMeter,common_setup_value,guarded_value,Rule5CommonOrdinary.runSelectedCommon,runCommon,runSource]
 split <;> simp_all

theorem common_calls (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) :
 (commonMeter cb W T S a b d q).calls=commonJobs T S a b d q := by
 simp only [commonMeter,common_setup_value,guarded_calls,commonJobs,sourceJobs]
 split <;> simp_all

theorem common_recursive (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) :
 (commonMeter cb W T S a b d q).recursiveWork=
 (((commonMeter cb W T S a b d q).calls).map (fun j=>W j.T j.S j.budget)).sum := by
 simp only [commonMeter]
 split
 · rfl
 · exact guarded_recursive _ _ _ _

def commonBudget (nt ns x : Nat) :=commonSetupBudget nt ns x+guardedBudget nt+3

theorem common_local (classFee : CheckRequest→Nat) (W : OrdinaryWork) {T S : Tree} {i e : RMAF.Vertex}
 {a b : Nat} {d : BadSelection} (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : (finalMeter classFee T S a b).value=some (.remaining d (.one e))) (q : Nat) :
 (commonMeter Rule5LocalWork.actual W T S a b d q).localWork≤commonBudget (leaves T).length (leaves S).length (subtreeLabels S d.badArc).length := by
 have setup:=common_setup_work classFee ch ad sel
 simp only [commonMeter]
 split
 · unfold commonBudget;dsimp only;omega
 · rename_i built hb
   have original : buildSetup T S (subtreeLabels S d.badArc) (outsideLabels S a b d) d.badArc=some built := by
    simpa only [common_setup_value] using hb
   have ident:=buildSetup_identity T S _ _ _ built original
   have r:=guarded_local W built q
   rw [ident.1] at r
   unfold commonBudget;dsimp only;omega

theorem common_call_progress (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat)
 {j : Job} (mem : j∈(commonMeter cb W T S a b d q).calls) :
 DepthOne.proper j.T j.S=true ∧ j.budget<q ∧ q-j.budget=1 := by
 rw [common_calls] at mem
 exact selected_one_job_progress T S a b d q j mem
end Universal233.Rule5ExecutionSource
