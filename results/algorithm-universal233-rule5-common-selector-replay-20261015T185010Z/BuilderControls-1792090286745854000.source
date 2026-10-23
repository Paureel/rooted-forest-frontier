import SourceProgram
namespace OrdinaryCommonSplit.Source.BuilderControls
open RMAF OrdinaryCommonSplit.GraphControls
theorem actual_builder : (buildSetup rootT rootS X Y [false,false]).map
    (fun d=>(d.x,d.y,d.rho,d.gamma))=some (0,3,6,7) := by decide
theorem ordinary_both_order_build : (buildSetup (.node tx ty) (.node tx ty) X Y [false]).isSome=true ∧
    (buildSetup (.node ty tx) (.node tx ty) X Y [false]).isSome=true := by decide
theorem invalid_source_side_rejected : buildSetup rootT rootS X Y []=none ∧
    (buildSetup rootT rootS X Y [true]).isNone=true := by decide
theorem duplicate_guard_rejected : (buildSetup rootT rootS [0,0,1,2] Y [false,false]).isNone=true := by decide
end OrdinaryCommonSplit.Source.BuilderControls
