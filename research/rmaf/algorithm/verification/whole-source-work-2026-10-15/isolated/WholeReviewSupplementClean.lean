import WholeReviewSourceBounds
import WorkControls
open RMAF VertexGeometry Universal233.CoreProgram Universal233.WholeSourceWork
 def sixteen : Owned := ⟨List.replicate 16 ⟨[[0]],[]⟩,0,0,0,0⟩
 def one : Owned := ⟨[⟨[[1]],[]⟩],0,0,0,0⟩
 theorem actual_copy16 : (appendOwned sixteen one).copied = 16 := by decide
 theorem formal_append18 : (appendOwned sixteen one).work = 18 := by decide
 theorem minimal_fine33 : (2*16+1 : Nat) = 33 := by decide
 theorem source_contract128 : (8*16 : Nat) = 128 := by decide
 def fixtureTarget : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5))
 theorem selector_returns_root : (meterCliqueSelection fixtureTarget [0,3] [1,4] [2,5]).value = some [] := by decide
 #print axioms actual_copy16
 #print axioms formal_append18
 #print axioms selector_returns_root
