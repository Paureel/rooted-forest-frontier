import OrdinaryPrepareBound
namespace OrdinaryDispatch.Hard2SourceWork.HandlerControls
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.FrontierWork
open Universal233.PaidQueries

def cross : Tree:=.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def T : Tree:=.node cross (.leaf 4)
def S : Tree:=.node (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.leaf 4)
def refused : GenericForest.FrontierWork.Ordinary:=fun _ _ _=>none

theorem owned_duplicate_occurrences :
 (ownedMeter [.leaf 0,.leaf 0,.leaf 1] [0]).value=[.leaf 0,.leaf 0] ∧
 0<(ownedMeter [.leaf 0,.leaf 0,.leaf 1] [0]).work:=by cbv

theorem local_restriction_literal :
 (localTargetMeter (some T) [0,2]).value=some (.node (.leaf 0) (.leaf 2)) ∧
 0<(localTargetMeter (some T) [0,2]).work:=by cbv

theorem repeated_union_has_copy_fee :
 (appendLabelsMeter [0,1] [2,3]).value=[0,1,2,3] ∧
 (appendLabelsMeter [0,1] [2,3]).work=8:=by cbv

theorem q1_refusal_paid :
 (goodPairLocalSource refused T S [0,1] [2,3] [4] 1).value.calls=[] ∧
 (goodPairLocalSource refused T S [0,1] [2,3] [4] 1).work=6:=by cbv

theorem q2_positive_dp_blocks_callback :
 (goodPairLocalSource refused T S [0,1] [2,3] [4] 2).value.answer=none ∧
 (goodPairLocalSource refused T S [0,1] [2,3] [4] 2).value.calls=[] ∧
 0<(goodPairLocalSource refused T S [0,1] [2,3] [4] 2).work:=by cbv

theorem q3_actual_residual_and_reconstruction :
 (goodPairLocalSource refused T S [0,1] [2,3] [4] 3).value.answer.map List.length=some 4 ∧
 ((goodPairLocalSource refused T S [0,1] [2,3] [4] 3).value.calls.map
   (fun a=>(ForestState.labels a.target,a.sources.map leaves,a.budget)))=[([4],[[4]],0)]:=by cbv

theorem q3_forest_local_debit_paid :
 (goodPairLocalSource refused T S [0,1] [2,3] [4] 3).work<
 (goodPairSource refused (fun _ _ _=>0) T S [0,1] [2,3] [4] 3).work:=by cbv

theorem proper_block_original_scans :
 (properBlockMeter (.leaf 0) (.leaf 0) [0]).value=true ∧
 (properBlockMeter (.leaf 0) (.leaf 0) [99]).value=false ∧
 0<(properBlockMeter (.leaf 0) (.leaf 0) [99]).work:=by cbv

theorem resolved_slot_literal :
 (ordinarySlotMeter (.leaf 0) (.leaf 0) [0]).value=some (Job.resolved [0] 0 [[0]]) ∧
 0<(ordinarySlotMeter (.leaf 0) (.leaf 0) [0]).work:=by cbv

theorem prepare_refuses_but_charges_tail :
 (ordinaryPrepareMeter (.leaf 0) (.leaf 0) [[0],[99],[0]]).value=none ∧
 (ordinarySlotMeter (.leaf 0) (.leaf 0) [99]).work<
 (ordinaryPrepareMeter (.leaf 0) (.leaf 0) [[0],[99],[0]]).work:=by cbv
end OrdinaryDispatch.Hard2SourceWork.HandlerControls
