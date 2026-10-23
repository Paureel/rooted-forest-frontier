import ERControls
namespace OrdinaryDispatch.EarlyLocalWork.Controls
open RMAF Universal233 WholeSourceWork GenericForest.CheckCorrespondence
open OrdinaryDispatch.FastOrdinary.Controls
-- Deliberately false source/control claims: each must be rejected by decide.
example : (3:Nat)+4=8 := by decide
example : (pretrace quartetT quartetS).checks.length=0 := by decide
example : (pretrace quartetT quartetS).tailSizes=[6,5,4,3,2,1] := by decide
example : toy.value=some 2 := by decide
example : toy.tailSizes=[2,0] := by decide
example : toy.work=0 := by decide
example : (meterSelect (.leaf 7) (.leaf 7)).work=0 := by decide
example : 1000≤(leaves (.leaf 7)).length := by decide
example : (meterRule4Select quartetT quartetS).value.isSome=false := by decide
example : OrdinaryDispatch.FastOrdinary.Controls.etag (meterEarly oneS oneT).value=3 := by decide
end OrdinaryDispatch.EarlyLocalWork.Controls
