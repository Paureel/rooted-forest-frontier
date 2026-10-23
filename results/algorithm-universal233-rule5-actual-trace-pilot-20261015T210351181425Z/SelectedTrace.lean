import CommonTrace
namespace Universal233.Rule5ActualTrace
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent
open CherryBranching Rule5Local Rule5Classification Rule5FinalClassification
open Rule5SourceOrientation Rule5OrdinaryDispatch
open GenericForest.FrontierWork

inductive Calls where
 | forestJobs (jobs : List ForestJob)
 | direct (jobs : List OrdinaryCommonSplit.Caller.Job)
 | paidRequests (jobs : List Rule5PaidSelector.PaidRequest)
 | selectorRefused
 | paidBuilderRefused
 deriving Repr, DecidableEq

structure Receipt where
 value : Rule5OrdinaryDispatch.Result
 calls : Calls
 deriving Repr, DecidableEq

def runForestJobs (actual : Ordinary) (T S : Tree) (q : Nat) (jobs : List ForestJob) : Option Forest :=
 best List.length (Rule5OrdinaryDispatch.accepted T S q)
   (jobs.filterMap fun j => GenericForest.solve actual j.target j.sources j.residual)

theorem runForestJobs_value (actual : Ordinary) (T S : Tree) (q : Nat) (cs : List Child) :
 runForestJobs actual T S q (forestJobs T q cs)=runChildren actual T S q cs := by
 rw [runForestJobs,runChildren,answers_are_literal_queries]

/-- Actual original request evaluation: cheap/full-state pretest resolution,
hard fallback or refusal has exactly the frozen currentAnswer semantics. -/
def runPaidRequests (actual : Ordinary) (T S : Tree) (q : Nat)
 (jobs : List Rule5PaidSelector.PaidRequest) : Option Forest :=
 best List.length (Rule5PaidOrdinary.originalAccepted T S q)
   (jobs.filterMap fun j => Rule5PaidOrdinary.currentAnswer actual (some j.target) j.sources j.residual)

def selectedTrace (actual : Ordinary) (T S : Tree) (a b q : Nat) : FinalSelection→Receipt
 | .prefix s =>
   let jobs := forestJobs T q (localChildren S a b s)
   ⟨.answered (runForestJobs actual T S q jobs),.forestJobs jobs⟩
 | .remaining d (.first _ _) =>
   let jobs := forestJobs T q (firstChildren S a b d)
   ⟨.answered (runForestJobs actual T S q jobs),.forestJobs jobs⟩
 | .remaining d (.third _ _) =>
   let jobs := forestJobs T q (thirdChildren S a b d)
   ⟨.answered (runForestJobs actual T S q jobs),.forestJobs jobs⟩
 | .remaining d (.one _) =>
   let r := commonTrace actual T S a b d q
   ⟨.answered r.value.join,.direct r.calls⟩
 | .remaining _ (.second _ _) =>
   match Rule5PaidSelector.buildSelected T S a b with
   | none => ⟨.paidBuilderRefused,.paidBuilderRefused⟩
   | some R =>
     let jobs := Rule5PaidSelector.requests R.geometry q
     ⟨.answered (runPaidRequests actual T S q jobs),.paidRequests jobs⟩

def dispatchTrace (actual : Ordinary) (T S : Tree) (a b q : Nat) : Receipt :=
 match selectFinal T S a b with
 | none => ⟨.selectorRefused,.selectorRefused⟩
 | some z => selectedTrace actual T S a b q z

theorem selected_value (actual : Ordinary) (T S : Tree) (a b q : Nat) (z : FinalSelection) :
 (selectedTrace actual T S a b q z).value=runSelected actual T S a b q z := by
 cases z with
 | «prefix» s => simp [selectedTrace,runSelected,runForestJobs_value]
 | remaining d z =>
   cases z with
   | first u v => simp [selectedTrace,runSelected,runForestJobs_value]
   | third u v => simp [selectedTrace,runSelected,runForestJobs_value]
   | one edge =>
     simp [selectedTrace,runSelected,common_value,Rule5CommonOrdinary.runSelectedCommon]
   | second u v =>
     cases built : Rule5PaidSelector.buildSelected T S a b <;>
       simp [selectedTrace,runSelected,Rule5PaidOrdinary.solveSelected,built,
         Rule5PaidOrdinary.bestFor,Rule5PaidOrdinary.answers,runPaidRequests]

theorem dispatch_value (actual : Ordinary) (T S : Tree) (a b q : Nat) :
 (dispatchTrace actual T S a b q).value=Rule5OrdinaryDispatch.dispatch actual T S a b q := by
 cases sel : selectFinal T S a b <;> simp [dispatchTrace,Rule5OrdinaryDispatch.dispatch,sel,selected_value]

def answer (r : Receipt) : Option Forest :=
 match r.value with | .answered F => F | _ => none

theorem rule5_value (actual : Ordinary) (T S : Tree) (a b q : Nat) :
 answer (dispatchTrace actual T S a b q)=OrdinaryDispatch.Hard2Dispatcher.rule5Answer actual T S a b q := by
 simp [answer,dispatch_value,OrdinaryDispatch.Hard2Dispatcher.rule5Answer]

/-- A paid query resolved by its real full-state0/1 pretest makes no ordinary
callback. Rejected hard queries retain the full actual forest frontier. -/
def currentFrontier (actual : Ordinary) (T : Option Tree) (ss : List Tree) (r : Nat) : List Query :=
 match ForestPretest01.pretest01 T ss with
 | .rejected => if r≤1 then [] else frontier actual T ss r
 | _ => []

def queries (actual : Ordinary) : Calls→List Query
 | .forestJobs jobs => jobs.flatMap fun j => frontier actual j.target j.sources j.residual
 | .direct jobs => directQueries jobs
 | .paidRequests jobs => jobs.flatMap fun j => currentFrontier actual (some j.target) j.sources j.residual
 | .selectorRefused => []
 | .paidBuilderRefused => []

theorem currentFrontier_member {actual : Ordinary} {T : Option Tree} {ss : List Tree} {r : Nat}
 {j : Query} (mem : j∈currentFrontier actual T ss r) :
 ForestPretest01.pretest01 T ss=.rejected ∧ 1<r ∧ j∈frontier actual T ss r := by
 cases pre : ForestPretest01.pretest01 T ss <;> simp [currentFrontier,pre] at mem
 split at mem
 · contradiction
 · exact ⟨rfl,by omega,mem⟩

theorem actual_common_calls (actual : Ordinary) (T S : Tree) (a b q : Nat) (d : BadSelection) (edge : RMAF.Vertex) :
 (selectedTrace actual T S a b q (.remaining d (.one edge))).calls=
   .direct (Rule5CommonSelector.commonJobs T S a b d q) := by
 simp [selectedTrace,common_calls]

theorem actual_second_calls (actual : Ordinary) (T S : Tree) (a b q : Nat) (d : BadSelection)
 (u v : RMAF.Vertex) {R : Rule5PaidSelector.SelectedPaid T S}
 (built : Rule5PaidSelector.buildSelected T S a b=some R) :
 (selectedTrace actual T S a b q (.remaining d (.second u v))).calls=
   .paidRequests (Rule5PaidSelector.requests R.geometry q) := by simp [selectedTrace,built]
end Universal233.Rule5ActualTrace
