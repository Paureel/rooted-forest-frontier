import CommonActualJobs
import Rule5PreControls
namespace Universal233.Rule5ClosedSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion OrdinaryDispatch.FastOrdinary OrdinaryDispatch.Hard2SourceWork
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5SelectedLocalWork
open ClassifierCheckFee PaidLiteralDecisionWork CherryBranching
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000

def t2 : Tree:=.node (.leaf 0) (.leaf 1)
def rep : Tree:=.node (.leaf 0) (.leaf 0)
def T9 : Tree:=Rule5Local.Pre.commonT
def S9 : Tree:=Rule5Local.Pre.commonS
def W17 (_ _ : Tree) (_ : Nat) : Nat:=17
def c9 : Candidate:=⟨[true,false],0,1,cuts S9 0 1⟩

theorem large_budget_domain : InputDomain t2 t2 99 2 99 1 := by
 exact ⟨by decide,by decide,by intro x hx;simp [t2,leaves] at hx;omega,by intro x hx;simp [t2,leaves] at hx;omega⟩

def controls : List (String×Bool):=
 [("concrete_embedding_fee_value",decide ((requestMeter (.embedding t2 [[0],[1]])).value=true) && decide (checkFee (.embedding t2 [[0],[1]])=(requestMeter (.embedding t2 [[0],[1]])).work)),
  ("concrete_false_embedding_fee",decide ((requestMeter (.embedding t2 [[0,1],[0]])).value=false) && decide (0<checkFee (.embedding t2 [[0,1],[0]]))),
  ("classifier_cap_polynomial",decide (checkCap 2=120*(2*2*2+2*2+2)^5+128*(2+1)^2+2)),
  ("literal_cap_polynomial",decide (literalBudget 2=1024*2^5+3072*2^4+960*2^3+640*2^2+238*2+164)),
  ("cutoff_equal_budget_refuses",decide (actualCallback 0 t2 t2 0=none)),
  ("cutoff_above_budget_refuses",decide (actualCallback 1 t2 t2 2=none)),
  ("cutoff_below_budget_exact_value",decide (actualCallback 1 t2 t2 0=OrdinaryDispatch.FastOrdinary.solve 0 t2 t2)),
  ("common_selected_admitted_fixture",decide (admitted T9 S9 0 1=true)),
  ("common_zero_budget_no_queries",decide ((calls (actualCallback 0) W17 T9 S9 0 1 0).length=0)),
  ("common_failed_answers_still_two_queries",decide ((actualRule5Source W17 T9 S9 0 1 1).value=none) && decide ((calls (actualCallback 1) W17 T9 S9 0 1 1).length=2)),
  ("common_exact_34_debit",decide ((actualRule5Source W17 T9 S9 0 1 1).work=(actualRule5Source (fun _ _ _=>0) T9 S9 0 1 1).work+34)),
  ("actual_wrapper_native_value",decide ((actualRule5Source W17 T9 S9 0 1 1).value=OrdinaryDispatch.Hard2Dispatcher.rule5Answer (actualCallback 1) T9 S9 0 1 1)),
  ("actual_wrapper_query_trace",decide (calls (actualCallback 1) W17 T9 S9 0 1 1=Rule5ActualTrace.queries (actualCallback 1) (Rule5ActualTrace.dispatchTrace (actualCallback 1) T9 S9 0 1 1).calls)),
  ("admitted_route_exact_value",decide ((admittedRouteSource W17 T9 S9 c9 1).value=executeHard2Route (actualCallback 1) T9 S9 c9 1 .admittedRule5)),
  ("malformed_wrapper_refuses",decide ((actualRule5Source W17 rep t2 0 1 2).value=none)),
  ("polynomial_coefficient_positive",decide (0<C5 0 0 0)),
  ("polynomial_coefficient_known_formula",decide (C5 2 3 1=prefixCap 2+80*(2^50*(2+3+1+2)^8)+4)),
  ("polynomial_monotone_planted",decide (C5 2 3 1≤C5 3 4 2)),
  ("actual_zero_counter_bound",decide (((actualRule5Source (fun _ _ _=>0) T9 S9 0 1 0).work:Rat)≤(C5 9 0 4:Rat))),
  ("actual_positive_counter_bound",decide (((actualRule5Source (fun _ _ _=>0) T9 S9 0 1 1).work:Rat)≤(C5 9 1 4:Rat)*(233/100:Rat))),
  ("q_not_bounded_by_reduced_leaves",decide (2<99) && decide (((actualRule5Source (fun _ _ _=>0) t2 t2 0 1 99).work:Rat)≤(C5 2 99 1:Rat)*(233/100:Rat)^99)),
  ("corrupt_zero_source_detected",let r:=actualRule5Source (fun _ _ _=>0) T9 S9 0 1 0;let bad:={r with work:=0};decide (bad.work≠r.work))]
#eval controls
#eval ("PASS_CLOSED_RULE5_SOURCE_CONTROLS",controls.length,controls.all Prod.snd)
end Universal233.Rule5ClosedSource
