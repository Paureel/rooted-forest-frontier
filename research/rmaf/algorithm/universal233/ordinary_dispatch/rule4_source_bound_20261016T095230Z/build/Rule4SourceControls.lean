import Rule4CallerSource
namespace OrdinaryDispatch.FullSourceWork.Rule4Controls
open RMAF Universal233 GenericForest.FrontierWork

def C : Tree := .node (.leaf 0) (.leaf 1)
def T : Tree := .node C (.node (.leaf 2) (.leaf 3))
def S : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def selected : Rule4.Choice T S := ⟨⟨0,1,2,[false,true],[true,true]⟩,by decide +kernel,by decide +kernel⟩
def refusal : GenericForest.FrontierWork.Ordinary := fun _ _ _=>none
def B : Rule4.Branch := ⟨C,C,[[false]],false⟩

theorem leaf_address_full_miss :
 (leafAddressMeter 0 C).work=8 ∧ (leafAddressMeter 9 C).work=12 ∧
 (leafAddressMeter 9 C).value=none := by cbv

theorem rejected_duplicates_and_null :
 (rule4AnswersSource refusal (fun _ _ _=>0) 0 [B,B]).work=13 ∧
 (rule4AnswersSource refusal (fun _ _ _=>0) 0 [B,B]).value=[] ∧
 (rule4AnswersSource refusal (fun _ _ _=>0) 0 []).work=1 := by cbv

theorem literal_empty_partition :
 (rule4PartitionMeter C [[false],[true]]).value=[[0],[1],[]] ∧
 (rule4StateMeter ⟨C,C,[[false],[true]],false⟩).value=[.leaf 0,.leaf 1] := by cbv

theorem selected_literal_costs :
 ((rule4BranchesMeter selected).value.map Rule4.Branch.cost)=[2,1,2] := by cbv

theorem selected_zero_output :
 (rule4Source refusal (fun _ _ _=>0) selected 0).value=none ∧
 0<(rule4Source refusal (fun _ _ _=>0) selected 0).work := by cbv
end OrdinaryDispatch.FullSourceWork.Rule4Controls
