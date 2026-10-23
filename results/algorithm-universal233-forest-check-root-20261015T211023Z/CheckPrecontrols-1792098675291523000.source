import FastExact
import Monomial
namespace GenericForest.CheckCorrespondence.Controls
open RMAF ForestState Universal233
set_option maxRecDepth 10000
def leaf : Tree := .leaf 0
def hostile (m : Nat) (_ _ : Tree) (_ : Nat) : Option (List (List Nat)) := some (List.replicate m [0])

theorem actual_checks : agrees (some leaf) [leaf] [[0]]=true ∧
 GenericForest.accepted (some leaf) [leaf] 0 [[0]]=true ∧
 GenericForest.accepted (some leaf) [leaf] 0 [[0],[0]]=false := by decide

theorem hostile_rejected : agreement leaf leaf (List.replicate 3 [0])=false ∧
 agrees (some leaf) [leaf] (List.replicate 3 [0])=false := by decide

theorem hostile_payload_size : ((List.replicate 3 [0]).flatten).length=3 ∧ (leaves leaf).length=1 ∧
 (List.replicate 3 [0]).flatten.count 0=3 := by decide

theorem actual_fast_success : OrdinaryDispatch.FastOrdinary.solve 0 leaf leaf=some [[0]] := by
 rw [OrdinaryDispatch.FastOrdinary.solve.eq_def]
 decide

def t3 : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def s3 : Tree := .node (.node (.leaf 0) (.leaf 2)) (.leaf 1)
theorem actual_fast_failure : OrdinaryDispatch.FastOrdinary.solve 0 t3 s3=none := by
 rw [OrdinaryDispatch.FastOrdinary.solve.eq_def]
 decide
end GenericForest.CheckCorrespondence.Controls
