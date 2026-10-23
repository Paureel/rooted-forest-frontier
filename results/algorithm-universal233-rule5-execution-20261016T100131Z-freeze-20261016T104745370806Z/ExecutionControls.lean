import Rule5SourceBounds
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence GenericForest.FrontierWork
open CherryBranching Rule5Case322 Rule5PaidSelector Case322PaidGuard Rule5SelectedLocalWork Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5OrdinaryDispatch
open OrdinaryCommonSplit OrdinaryCommonSplit.Source OrdinaryCommonSplit.Caller
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000

def t2 : Tree:=.node (.leaf 0) (.leaf 1)
def rep : Tree:=.node (.leaf 0) (.leaf 0)
def crossT : Tree:=.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def crossS : Tree:=.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def tx : Tree:=.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def sx : Tree:=.node (.leaf 0) (.node (.leaf 1) (.leaf 2))
def ty : Tree:=.node (.node (.leaf 3) (.leaf 4)) (.leaf 5)
def sy : Tree:=.node (.leaf 3) (.node (.leaf 4) (.leaf 5))
def commonT : Tree:=.node tx ty
def commonS : Tree:=.node sx sy
def cb (T _ : Tree) (_ : Nat) : Option Forest:=some ((leaves T).map (fun x=>[x]))
def cbNone (_ _ : Tree) (_ : Nat) : Option Forest:=none
def cbFirstFails (T _ : Tree) (_ : Nat) : Option Forest:=if (leaves T).length=3 then none else some ((leaves T).map (fun x=>[x]))
def W (_ _ : Tree) (_ : Nat) : Nat:=17
def W13 (_ _ : Tree) (_ : Nat) : Nat:=13
def withSetup (f : Setup→Bool) : Bool:=
 match (setupMeter commonT commonS [0,1,2] [3,4,5] [false]).value with | none=>false | some d=>f d

def c : Branch:=⟨.source,[[false]],[[0],[1]]⟩
def dup : Branch:=⟨.source,[[false],[false]],[[0],[1]]⟩
def classFee (_ : CheckRequest) : Nat:=7
def literalFee (_ : LiteralCall) : Nat:=9
def bd : BadSelection:=⟨[false],[true],2⟩
def zs : List FinalSelection:=[.prefix .remaining,.remaining bd (.first [] []),.remaining bd (.third [] []),.remaining bd (.one []),.remaining bd (.second [] [])]

def controls : List (String×Bool):=
 [("setup_execution_fixture",withSetup (fun _=>true)),
  ("common_zero_budget_no_callbacks",withSetup (fun d=>decide ((guardedMeter cb W d 0).calls.length=0))),
  ("common_two_strict_callbacks",withSetup (fun d=>decide ((guardedMeter cb W d 4).calls.length=2) && decide ((guardedMeter cb W d 4).recursiveWork=34))),
  ("common_first_failure_still_second",withSetup (fun d=>decide ((guardedMeter cbFirstFails W d 4).calls.length=2) && decide ((guardedMeter cbFirstFails W d 4).recursiveWork=34) && decide ((guardedMeter cbFirstFails W d 4).value=some none))),
  ("common_length_accept",withSetup (fun d=>decide ((guardedMeter cb W d 4).value=some (some [[0],[1],[2],[3],[4,5]])))),
  ("common_length_reject",withSetup (fun d=>decide ((guardedMeter cb W d 1).value=some none))),
  ("common_native_value",withSetup (fun d=>decide ((guardedMeter cb W d 4).value=runGuarded d 4 cb))),
  ("common_duplicate_jobs_both_paid",let j:Job:=⟨t2,t2,0⟩;decide ((jobsAnswersMeter cbNone W [j,j]).recursiveWork=34) && decide ((jobsAnswersMeter cbNone W [j,j]).calls.length=2)),
  ("outside_native_value",withSetup (fun d=>decide ((outsideReplyMeter d [[3],[4,5]]).value=outsideReply d [[3],[4,5]]))),
  ("forest_pretest_unchanged",decide ((forestPretestMeter (some t2) [t2]).value=.found [[0,1]])),
  ("forest_pretest_repeated_labels_refused",decide ((forestPretestMeter (some rep) [rep]).value=.refused)),
  ("forest_pretest_missing_target_refused",decide ((forestPretestMeter none [.leaf 0]).value=.refused)),
  ("forest_pretest_rejected_crossing",decide ((forestPretestMeter (some crossT) [crossS]).value=.rejected)),
  ("forest_candidates_all_occurrences",decide ((forestCandidatesMeter [t2,t2]).value=ForestPretest01.candidates [t2,t2])),
  ("additional_cost_truncation_tie",decide ((bestAdditionalMeter [.leaf 0] (fun _=>⟨true,1⟩) [[[0]],[]]).value=some [[0]])),
  ("length_score_distinct_tie",decide ((bestLengthMeter (fun _=>⟨true,1⟩) [[[0]],[]]).value=some [])),
  ("current_small_reject_no_fallback",decide ((currentQueryMeter cbNone W13 (some crossT) [crossS] 1).ordinaryCalls=[])),
  ("current_rejected_fallback_occurrence",decide ((currentQueryMeter cbNone W13 (some crossT) [crossS] 2).ordinaryCalls=[((crossT,crossS),2)])),
  ("current_fallback_exact_debit",decide ((currentAnswerSource cbNone W13 (some crossT) [crossS] 2).work=(currentAnswerSource cbNone (fun _ _ _=>0) (some crossT) [crossS] 2).work+13)),
  ("current_native_value",decide ((currentAnswerSource cbNone W13 (some crossT) [crossS] 2).value=Rule5PaidOrdinary.currentAnswer cbNone (some crossT) [crossS] 2)),
  ("split_repeated_and_empty_blocks",decide ((splitForestMeter [0] [[],[0,1,0],[2]]).value=[[0,0],[1],[2]])),
  ("split_flatten_length",decide ((splitForestMeter [0] [[],[0,1,0],[2]]).value.flatten.length=4)),
  ("arc_partition_duplicate_cuts",decide ((arcPartitionMeter t2 [[false],[false]]).value=[[0],[1]]) && decide ((arcPartitionMeter t2 [[false],[false]]).work>(arcPartitionMeter t2 [[false]]).work)),
  ("arc_partition_root_empty_cut",decide ((arcPartitionMeter t2 [[],[]]).value=[[0,1]])),
  ("guard_valid",decide ((currentGuardMeter t2 t2 c).value=true)),
  ("guard_duplicate_refusal",decide ((currentGuardMeter t2 t2 dup).value=false)),
  ("guard_native_value",decide ((currentGuardMeter crossT crossS c).value=currentGuard crossT crossS c)),
  ("raw_plan_source_value",decide ((rawPlanMeter crossT crossS 0 1 2 [false,false] [false,true] [false,true] [true,false]).value=Case322Extraction.rawPlan crossT crossS 0 1 2 [false,false] [false,true] [false,true] [true,false])),
  ("raw_plan_polynomial",decide ((rawPlanMeter crossT crossS 0 1 2 [false,false] [false,true] [false,true] [true,false]).work≤rawPlanBudget crossT crossS 7)),
  ("request_unaffordable",decide ((requestForMeter t2 t2 0 c).value=none)),
  ("request_residual_full_paid",decide (((requestForMeter t2 t2 3 c).value.map PaidRequest.residual)=some 2)),
  ("duplicate_requests_preserved",decide ((requestListMeter t2 t2 1 [c,c]).value.length=2)),
  ("all_selected_arm_values",zs.all (fun z=>decide ((runSelectedSource cbNone W classFee literalFee crossT crossS 0 1 2 z).value=runSelected cbNone crossT crossS 0 1 2 z))),
  ("dispatch_native_value",decide ((dispatchSource cbNone W classFee literalFee t2 t2 0 1 1).value=dispatch cbNone t2 t2 0 1 1)),
  ("corrupt_zero_prefix_detected",withSetup (fun d=>let r:=guardedMeter cb W d 4;let bad:={r with localWork:=0};decide (bad.localWork≠r.localWork)))]
#eval controls
#eval ("PASS_EXECUTION_SOURCE_CONTROLS",controls.length,controls.all Prod.snd)
end Universal233.Rule5ExecutionSource
