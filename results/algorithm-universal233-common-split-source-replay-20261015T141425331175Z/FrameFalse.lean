import ActualFrameControls
open OrdinaryCommonSplit.Source OrdinaryCommonSplit.Source.ActualFrameControls
example : runSource rootT S X Y sourceArc 0 (fun _ _ _=>none)=none := by decide
example : incident rootT X=[[false]] := by decide
