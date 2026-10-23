import OverheadBound
import FrontierPrecontrols
namespace GenericForest.FrontierControls
open RMAF ForestState Universal233 Universal233.PaidQueries GenericForest.FrontierWork
set_option maxRecDepth 10000
def target3 : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def source3 : Tree := .node (.node (.leaf 0) (.leaf 2)) (.leaf 1)
def noOrd (_ _ : Tree) (_ : Nat) : Option Forest := none

theorem singleton_literal : frontier noOrd (some target3) [source3] 2=[((target3,source3),2)] := by decide +kernel

theorem solved_literal : frontier noOrd (some target3) [target3] 2=[] := by decide +kernel

theorem malformed_literal : frontier noOrd (some target3) [.leaf 0,.leaf 0] 2=[] := by decide +kernel

theorem ordinary_work_once : queryWork (fun _ _ _=>3) (frontier noOrd (some target3) [source3] 2)=3 := by decide +kernel

theorem source_split_planted : sourceWork noOrd (fun _ _ _=>3) (some target3) [source3] 2=
 sourceWork noOrd (fun _ _ _=>0) (some target3) [source3] 2+3 := by decide +kernel

def target4 : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def crossed : List Tree := [.node (.leaf 0) (.leaf 2),.node (.leaf 1) (.leaf 3)]
theorem overlap_literal :
 (overlap target4 crossed).isSome=true ∧
 ((overlap target4 crossed).toList.flatMap fun h=>branches target4 crossed h 1).length=2 ∧
 ((overlap target4 crossed).toList.flatMap fun h=>branches target4 crossed h 1).all (fun io=>io.2.sourceCuts.length==1)=true := by decide +kernel

theorem actual_geometric_three : geometric 3=3 := by decide +kernel

theorem source_equations_all_inputs (actual : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (q : Nat) :
 sourceWork actual W T ss q=sourceWork actual (fun _ _ _=>0) T ss q+queryWorkRat W (frontier actual T ss q) :=
 source_work_split actual W T ss q
end GenericForest.FrontierControls
