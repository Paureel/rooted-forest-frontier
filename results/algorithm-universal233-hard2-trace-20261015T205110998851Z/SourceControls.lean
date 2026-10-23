import SourceDefs
namespace OrdinaryCommonSplit.Source.Controls
open RMAF OrdinaryCommonSplit.GraphControls
theorem actual_root_and_descendant : incident rootT X=[[false,false]] ∧
    incident rootS X=[[false,false]] := by decide
theorem actual_nonzero_cuts : Universal233.DepthOne.subtreeLabels rootT [false,false]=Y ∧
    Universal233.DepthOne.subtreeLabels rootS [false,false]=X := by decide
theorem literal_nontrivial_partition : partitionCheck (leaves rootT) [X,Y]=true ∧
    partitionCheck (leaves rootS) [X,Y]=true := by decide
theorem descendant_other_orientation : incident (.node tx ty) X=[[false]] ∧
    incident (.node ty tx) X=[[true]] := by decide
end OrdinaryCommonSplit.Source.Controls
