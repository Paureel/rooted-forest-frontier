import NumericControls
open RMAF ForestState OrdinaryDispatch.GlobalNumeric.Controls
example : OrdinaryDispatch.commonFresh (.node (.leaf 3) (.leaf 9))=9 := by cbv
example : (OrdinaryDispatch.WorkIntegration.forestQueries (fun _ _ _=>none) repeated).length=1 := by cbv
example : GenericForest.CheckCorrespondence.labelBits (0-1)=0 := by cbv
example : (List.replicate (3+1) false).length≤3 := by decide
