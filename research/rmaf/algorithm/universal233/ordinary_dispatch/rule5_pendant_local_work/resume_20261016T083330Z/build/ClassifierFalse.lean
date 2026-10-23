import ClassifierControls
namespace Universal233.Rule5PendantLocalWork
open RMAF Rule5FinalClassification
example : (incidentMeter (.leaf 0) []).work=0 := by decide
example : (boundaryMeter comb4 [0,2] 1).value=some (.third [false] [false,false,true]) := by decide
example : (optionsMeter rejectOption [0,0]).work=(optionsMeter rejectOption [0]).work := by decide
example : (finalMeter fee repeated repeated 0 0).work=0 := by decide
end Universal233.Rule5PendantLocalWork
