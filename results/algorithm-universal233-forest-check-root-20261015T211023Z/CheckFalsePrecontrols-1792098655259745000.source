import CheckPrecontrols
namespace GenericForest.CheckCorrespondence.Controls
open RMAF ForestState Universal233
example : agrees (some leaf) [leaf] (List.replicate 3 [0])=true := by decide
example : ((List.replicate 3 [0]).flatten).length≤(leaves leaf).length := by decide
example : (List.replicate 3 [0]).flatten.count 0=1 := by decide
example : GenericForest.accepted (some leaf) [leaf] 0 [[0],[0]]=true := by decide
end GenericForest.CheckCorrespondence.Controls
