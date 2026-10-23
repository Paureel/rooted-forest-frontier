import Controls
namespace Universal233.SourceCoverage.FalseControls
open RMAF CoreProgram
-- Must be rejected: a queried over-budget continuation is a prune, no emission.
theorem false_budget_zero : (generate CoreProgram.Controls.cherry3 id 0).outputs.length = 1 := by decide
end Universal233.SourceCoverage.FalseControls
