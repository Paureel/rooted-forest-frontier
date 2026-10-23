import ForestResource
import BoundedFrontier
namespace GenericForest.LocalPolynomial.Controls
open RMAF ForestState Universal233 Universal233.CoreProgram Universal233.CoreWork Universal233.WholeSourceWork
set_option maxRecDepth 10000
def tree : Tree := .node (.leaf 0) (.leaf 1)
theorem nodes_planted : treeNodes tree=3 ∧ sourceNodes [tree]+1=4 := by decide

theorem prefix_bill_retained : (meterGenerate tree id 0).measured.work>initialCharge tree ∧
 (meterGenerate tree id 0).measured.prunedCalls>0 ∧ (meterGenerate tree id 0).measured.receipt.outputs=[] := by decide +kernel

theorem color_bill_positive : (meterColorLabel tree [] 0).work>0 := by decide

theorem materialization_bill_positive : materializationBill tree [tree] 1 0 ⟨[[0],[1]],[[false]]⟩>inspectionBill (some tree) [tree] 1 := by decide +kernel

theorem boundary_inspection : inspectionBill none [] 0=4096 := by decide
end GenericForest.LocalPolynomial.Controls
