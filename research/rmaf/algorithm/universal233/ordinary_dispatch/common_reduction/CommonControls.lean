import CommonDispatch
namespace OrdinaryDispatch.CommonControls
open RMAF Universal233 Universal233.CherryBranching ForestState

def callback (T S : Tree) (q : Nat) : Option CommonForest :=
 match DepthOne.pretest01 T S with
 | .found c => if DepthOne.cutCost c≤q then some (DepthOne.forest S c) else none
 | _ => none

def T : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.node (.leaf 3) (.leaf 4)))
def S : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 3) (.node (.leaf 2) (.leaf 4)))
def same : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def c : Candidate := ⟨[false],0,1,[]⟩

theorem proper_fixture : proper (some T) [S]=true := by decide
theorem selected_actual_fixture : select T S=some (.common,c) := by decide
theorem rejected_zero : runCommonCherry callback T S c 0=none := by cbv
theorem found_one : (runCommonCherry callback T S c 1).map (fun F=>(agreement T S F,F.length))=some (true,2) := by cbv
theorem same_zero : (runCommonCherry callback same same c 0).map (fun F=>(agreement same same F,F.length))=some (true,1) := by cbv
theorem strict_four : (leaves (contract c.a c.b (commonFresh T) T)).length=4 := by decide
end OrdinaryDispatch.CommonControls
