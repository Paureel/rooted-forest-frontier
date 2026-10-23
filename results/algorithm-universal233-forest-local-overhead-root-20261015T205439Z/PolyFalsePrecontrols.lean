import PolyPrecontrols
namespace GenericForest.LocalPolynomial.Controls
open RMAF ForestState Universal233 Universal233.CoreProgram Universal233.CoreWork Universal233.WholeSourceWork
example : treeNodes tree=2 := by decide
example : (meterGenerate tree id 0).measured.prunedCalls=0 := by decide
example : (meterColorLabel tree [] 0).work=0 := by decide
example : inspectionBill none [] 0=0 := by decide
end GenericForest.LocalPolynomial.Controls
