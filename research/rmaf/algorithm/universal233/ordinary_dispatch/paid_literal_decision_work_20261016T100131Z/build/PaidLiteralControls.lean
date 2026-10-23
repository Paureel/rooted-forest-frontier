import LiteralBinding
namespace Universal233.PaidLiteralDecisionWork
open RMAF CoreGraph HardParent CoreWork Rule5PrefixLocalWork Rule5PendantLocalWork Rule5RemainingLocalWork
open Rule5PaidSelector Rule5Classification Rule5FinalClassification Case322PaidGuard Case322Extraction
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000

def plantedX : Tree:=.node (.leaf 3) (.leaf 4)
def plantedCore : Tree:=.node (.leaf 0) (.leaf 1)
def plantedT : Tree:=.node (.node plantedCore (.leaf 3)) (.node (.leaf 2) (.leaf 4))
def plantedS : Tree:=bottom false false false 0 1 2 plantedX
def plantedD : BadSelection:=⟨[false,false,true],[false,true],2⟩
def plantedRow : BottomData:=⟨[],false,false,false,0,1,plantedX⟩
def plantedU : RMAF.Vertex:=[true,false]
def plantedV : RMAF.Vertex:=[false,false]
def plantedQa : RMAF.Vertex:=[false,false,false]
def plantedUb : RMAF.Vertex:=[false,false,true]
def plantedCall : LiteralCall:=⟨plantedRow,plantedCore,plantedQa,plantedUb,plantedD,plantedU,plantedV⟩

theorem planted_domain : LiteralCallDomain plantedT plantedS 0 1 plantedD plantedU plantedV plantedCall := by
 unfold LiteralCallDomain
 decide

theorem planted_literal : LiteralProps plantedT plantedS 0 1 plantedD plantedU plantedV plantedRow plantedCore plantedQa plantedUb := by
 decide

def controls : List (String×Bool):=
 [("conjunction_empty",(checksMeter []).value),
  ("conjunction_true",(checksMeter [fun _=>⟨true,1⟩,fun _=>⟨true,1⟩]).value),
  ("conjunction_false",!(checksMeter [fun _=>⟨false,1⟩,fun _=>⟨true,1⟩]).value),
  ("scalar_equal",(natEqMeter 0 0).value),
  ("scalar_unequal",!(natEqMeter 0 1).value),
  ("list_empty",(natListEqMeter [] []).value),
  ("list_matching",(natListEqMeter [0,1,0] [0,1,0]).value),
  ("list_wrong_order",!(natListEqMeter [0,1] [1,0]).value),
  ("tree_equal",(treeEqMeter plantedT plantedT).value),
  ("tree_wrong_label",!(treeEqMeter (.leaf 0) (.leaf 1)).value),
  ("bounded_exists_empty",!(anyMeter (fun (_:Nat)=>⟨true,1⟩) []).value),
  ("bounded_forall_empty",(allMeter (fun (_:Nat)=>⟨false,1⟩) []).value),
  ("literal_success",(literalMeter plantedT plantedS 0 1 plantedD plantedU plantedV plantedRow plantedCore plantedQa plantedUb).value),
  ("literal_success_frozen_decision",decide (LiteralProps plantedT plantedS 0 1 plantedD plantedU plantedV plantedRow plantedCore plantedQa plantedUb)),
  ("literal_success_bound",decide (literalFee plantedT plantedS 0 1 plantedCall≤literalBudget 10)),
  ("duplicate_target_refusal",!(literalMeter (.node (.leaf 0) (.leaf 0)) plantedS 0 1 plantedD plantedU plantedV plantedRow plantedCore plantedQa plantedUb).value),
  ("source_leaf_address_refusal",!(literalMeter plantedT plantedS 0 1 plantedD plantedU plantedV {plantedRow with w:=[true]} plantedCore plantedQa plantedUb).value),
  ("wrong_label_partition_refusal",!(labelsMeter plantedT plantedCore plantedX 99).value),
  ("wrong_boundary_refusal",!(boundaryEqMeter plantedS plantedX [true]).value),
  ("minimal_off_root_refusal",!(minimalMemMeter plantedT plantedX plantedU).value),
  ("corrupt_zero_fee_detected",decide (literalFee plantedT plantedS 0 1 plantedCall≠0)),
  ("exact_value_success",decide ((literalMeter plantedT plantedS 0 1 plantedD plantedU plantedV plantedRow plantedCore plantedQa plantedUb).value=decide (LiteralProps plantedT plantedS 0 1 plantedD plantedU plantedV plantedRow plantedCore plantedQa plantedUb)))]
#eval controls
#eval ("LITERAL_CONTROLS",controls.length,controls.all Prod.snd)
#eval ("PLANTED_SUCCESS_WORK",literalFee plantedT plantedS 0 1 plantedCall,"UNIFORM_CAP_N10",literalBudget 10)
#print axioms literal_value
#print axioms literal_work
#print axioms literal_call_work
#print axioms paid_selected_work_concrete
end Universal233.PaidLiteralDecisionWork
