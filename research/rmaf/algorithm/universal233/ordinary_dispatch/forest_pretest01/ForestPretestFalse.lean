import ForestCoverageControls
namespace ForestPretest01.Controls
open RMAF ForestState ForestPretest01
example : agrees (some t) ss (unchanged ss) = true := by decide
example : pretest01 (some rejectT) rejectSS ≠ .rejected := by decide
example : omitFirst.any coversWitness = true := by decide
example : pretest01 none [.leaf 9] ≠ .refused := by decide
end ForestPretest01.Controls
