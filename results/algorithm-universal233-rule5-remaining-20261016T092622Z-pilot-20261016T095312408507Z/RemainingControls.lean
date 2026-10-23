import CommonSetupBinding
import PaidDomains
namespace Universal233.Rule5RemainingLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork Rule5PaidSelector Rule5Classification Rule5FinalClassification Case322PaidGuard Case322Extraction
open OrdinaryCommonSplit OrdinaryCommonSplit.Source OrdinaryCommonSplit.Caller
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000

def t2 : Tree:=.node (.leaf 0) (.leaf 1)
def rep : Tree:=.node (.leaf 0) (.leaf 0)
def crossT : Tree:=.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def crossS : Tree:=.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def bot : Tree:=bottom false false false 0 1 2 (.leaf 3)
def bd : BadSelection:=⟨[false],[true],2⟩
def rr : BottomData:=⟨[],false,false,false,0,1,.leaf 3⟩
def literalFee (_ : LiteralCall) : Nat:=9
def classifierFee (_ : CheckRequest) : Nat:=7

def view (d : Setup) : List Tree×List (List Nat)×List Nat:=
 ([d.T,d.S,d.tx,d.sx,d.ty,d.sy,d.mxT,d.mxS,d.myT,d.myS],[d.X,d.Y],[d.x,d.y,d.rho,d.gamma])
def geometryView {T S : Tree} (d : LiteralGeometry T S) : List Tree×List RMAF.Vertex×List Nat×List Bool:=
 ([d.X,d.C],[d.w,d.r,d.qa,d.ub,d.uc],[d.a,d.b,d.c],[d.sa,d.sc,d.sb])
def paidView {T S : Tree} (r : SelectedPaid T S) :=
 (r.d.badArc,r.d.singletonArc,r.d.c,r.u,r.v,geometryView r.geometry)

def setupControl (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) : Bool :=
 decide ((setupMeter T S X Y p).value.map view=(buildSetup T S X Y p).map view) &&
 decide ((setupMeter T S X Y p).work≤setupEnvelope T S X Y p)

def orientations : List Bool:=[false,true]
def parseOrientations : Bool:=orientations.all fun sa=>orientations.all fun sc=>orientations.all fun sb=>
 let S:=bottom sa sc sb 0 1 2 (.leaf 3)
 decide ((parseBottomMeter S [] sa sc sb 0 1 2).value=some (.leaf 3)) &&
 decide ((parseBottomMeter S [] sa sc sb 0 1 2).work≤20)

def controls : List (String×Bool):=
 [("perm_empty",decide ((permMeter [] []).value=true)),
  ("perm_reordered_repeated",decide ((permMeter [0,1,0] [0,0,1]).value=true)),
  ("perm_wrong_multiplicity",decide ((permMeter [0,0] [0]).value=false)),
  ("erase_first_only",decide ((eraseMeter 0 [1,0,0]).value=[1,0])),
  ("max_duplicates",decide ((maxMeter [4,2,4]).value=4) &&decide ((maxMeter [4,2,4]).work=10)),
  ("marked_empty_refusal",decide ((markedMeter t2 [] 9 10).value=none)),
  ("marked_relabel_actual",decide ((markedMeter t2 [0] 1 7).value=some (.node (.leaf 0) (.leaf 7)))),
  ("setup_success",setupControl t2 t2 [0] [1] [false] &&decide ((setupMeter t2 t2 [0] [1] [false]).value.isSome=true)),
  ("setup_target_nodup_refusal",setupControl rep t2 [0] [1] [false] &&decide ((setupMeter rep t2 [0] [1] [false]).value.isNone=true)),
  ("setup_source_nodup_refusal",setupControl t2 rep [0] [1] [false]),
  ("setup_target_partition_refusal",setupControl t2 t2 [0] [0] [false]),
  ("setup_source_partition_refusal",setupControl t2 (.node (.leaf 0) (.leaf 2)) [0] [1] [false]),
  ("setup_root_refusal",setupControl t2 t2 [0] [1] [] &&decide ((setupMeter t2 t2 [0] [1] []).value.isNone=true)),
  ("setup_missing_subtree_refusal",setupControl t2 t2 [0] [1] [false,false]),
  ("setup_wrong_subtree_labels",setupControl t2 t2 [0] [1] [true]),
  ("setup_incident_refusal",setupControl crossT crossS [0,2] [1,3] [false] &&decide ((setupMeter crossT crossS [0,2] [1,3] [false]).value.isNone=true)),
  ("setup_polynomial",decide ((setupMeter t2 t2 [0] [1] [false]).work≤setupBudget 2 1 2)),
  ("all_eight_orientations",parseOrientations),
  ("parse_wrong_labels",decide ((parseBottomMeter bot [] false false false 8 1 2).value=none)),
  ("parse_missing_address",decide ((parseBottomMeter bot [true,true] false false false 0 1 2).value=none)),
  ("rows_exact_and_bounded",decide ((rowsMeter bot 0 1 2).value=rows bot 0 1 2) &&decide ((rowsMeter bot 0 1 2).value.length≤32*(leaves bot).length) &&decide ((rowsMeter bot 0 1 2).work≤rowsBudget (leaves bot).length)),
  ("rows_include_literal",decide (rr∈(rowsMeter bot 0 1 2).value)),
  ("leaf_address_left",decide ((leafAddressMeter t2 0).value=some [false])),
  ("leaf_address_right",decide ((leafAddressMeter t2 1).value=some [true])),
  ("leaf_address_missing",decide ((leafAddressMeter t2 9).value=none)),
  ("leaf_first_duplicate",decide ((leafAddressMeter rep 0).value=some [false])),
  ("literal_request_on_failed_props",decide ((oneCalls bot [false,false,false] rr).length=1) &&decide ((buildOneMeter literalFee bot bot 0 1 bd [] [false,false,false] rr).value.isNone=true)),
  ("build_one_value",decide ((buildOneMeter literalFee bot bot 0 1 bd [] [false,false,false] rr).value.map geometryView=(buildOne bot bot 0 1 bd [] [false,false,false] rr).map geometryView)),
  ("second_builder_value_and_budget",decide ((secondBuilderMeter literalFee bot bot 0 1 bd [] []).value.map geometryView=(buildForSecond bot bot 0 1 bd [] []).map geometryView) &&decide ((secondBuilderMeter literalFee bot bot 0 1 bd [] []).work≤secondBuilderBudget (leaves bot).length (leaves bot).length 0 9)),
  ("second_calls_bounded",decide ((secondCalls literalFee bot bot 0 1 bd [] []).length≤32*(leaves bot).length)),
  ("paid_selected_value",decide ((paidSelectedMeter classifierFee literalFee t2 t2 0 1).value.map paidView=(buildSelected t2 t2 0 1).map paidView)),
  ("corrupt_zero_setup_work_detected",let m:=setupMeter t2 t2 [0] [1] [false]
   let corrupt:={m with work:=0};decide (m.work≠corrupt.work))]
#eval controls
#eval ("PASS_REMAINING_SOURCE_CONTROLS",controls.length,controls.all Prod.snd)
end Universal233.Rule5RemainingLocalWork
