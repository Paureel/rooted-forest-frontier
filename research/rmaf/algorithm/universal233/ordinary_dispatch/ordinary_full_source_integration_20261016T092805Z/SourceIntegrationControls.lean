import OrdinarySimpleTreeSource
import SelectedAgreementBinding
import Rule4CallerSource
import FullSourceControls
namespace OrdinaryDispatch.FullSourceWork.IntegrationControls
open RMAF ForestState Universal233 GenericForest.FrontierWork
open OrdinaryDispatch.WorkRecursion Universal233.Rule5SelectedLocalWork

def refused : GenericForest.FrontierWork.Ordinary:=fun _ _ _=>none
def c : CherryBranching.Child:=
 ⟨[leaves Hard2Dispatcher.Controls.S],[Hard2Dispatcher.Controls.S],1⟩

theorem duplicate_failed_queries :
 (childrenTrace refused Hard2Dispatcher.Controls.T Hard2Dispatcher.Controls.S 1 [c,c]).queries=
 [((Hard2Dispatcher.Controls.T,Hard2Dispatcher.Controls.S),0),
  ((Hard2Dispatcher.Controls.T,Hard2Dispatcher.Controls.S),0)] := by cbv

theorem failed_duplicate_charged :
 (runChildrenSource refused (fun _ _ _=>1) Hard2Dispatcher.Controls.T Hard2Dispatcher.Controls.S 1 [c,c]).value=none ∧
 (runChildrenSource refused (fun _ _ _=>1) Hard2Dispatcher.Controls.T Hard2Dispatcher.Controls.S 1 [c,c]).work=
 (runChildrenSource refused (fun _ _ _=>0) Hard2Dispatcher.Controls.T Hard2Dispatcher.Controls.S 1 [c,c]).work+2 := by
 constructor
 · rw [runChildrenSource_value];cbv
 · rw [runChildrenSource_split,duplicate_failed_queries]
   simp [queryWork]

theorem unaffordable_no_forest_debit :
 childForestDebit refused (fun _ _ _=>77) Hard2Dispatcher.Controls.T 0 [c,c]=0 ∧
 (childrenAnswersMeter refused (fun _=>77) Hard2Dispatcher.Controls.T 0 [c,c]).localWork=11 := by cbv

theorem literal_empty_region :
 (rule4PartitionMeter (.node (.leaf 0) (.leaf 1)) [[false],[true]]).value=[[0],[1],[]] ∧
 (rule4StateMeter ⟨.node (.leaf 0) (.leaf 1),.node (.leaf 0) (.leaf 1),[[false],[true]],false⟩).value=[.leaf 0,.leaf 1] ∧
 0<(rule4PartitionMeter (.node (.leaf 0) (.leaf 1)) [[false],[true]]).work := by cbv

theorem actual_simple_leaf_subtotal :
 simpleTreeSource 9 (.leaf 0) (.leaf 0)=0 ∧
 sourceSubtotal (fun _ _ _=>5) 9 (.leaf 0) (.leaf 0)=5 := by cbv

theorem child_materialization_literal :
 (branchesMeter (.node (.leaf 0) (.leaf 1)) 0 1).value.length=3 ∧
 0<(highSource refused (fun _ _ _=>0) (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) 0 0 1).work := by cbv
end OrdinaryDispatch.FullSourceWork.IntegrationControls
