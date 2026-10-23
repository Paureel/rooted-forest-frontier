import ScaffoldExact
namespace OrdinaryScaffold.Controls
open RMAF ForestState Universal233 Universal233.CherryBranching OrdinaryDispatch

def T : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def S : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def graftT : Tree := .node (.node (.leaf 4) (.leaf 5)) T
def graftS : Tree := .node (.node (.leaf 4) (.leaf 5)) S
def c : Candidate := ⟨[false],4,5,[]⟩

theorem quartet_reject_one : solve 1 T S=none := by cbv
theorem quartet_found_two : (solve 2 T S).map (fun F=>(agreement T S F,F.length))=some (true,3) := by cbv
theorem same_zero : (solve 0 T T).map (fun F=>(agreement T T F,F.length))=some (true,1) := by cbv
theorem malformed_none : solve 2 (.leaf 0) (.leaf 1)=none := by cbv
theorem graft_rejected : DepthOne.pretest01 graftT graftS=.rejected := by decide
theorem graft_selected_common : select graftT graftS=some (.common,c) := by decide
theorem graft_contract_five : (leaves (contract c.a c.b (commonFresh graftT) graftT)).length=5 := by decide
theorem graft_found_two : (solve 2 graftT graftS).map (fun F=>(agreement graftT graftS F,F.length))=some (true,3) := by cbv
end OrdinaryScaffold.Controls
