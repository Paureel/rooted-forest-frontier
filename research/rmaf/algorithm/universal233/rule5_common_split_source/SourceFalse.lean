import SourceControls
open OrdinaryCommonSplit.Source OrdinaryCommonSplit.GraphControls
example : Universal233.DepthOne.subtreeLabels rootT [false,false]=X := by decide
example : incident rootT X=[] := by decide
