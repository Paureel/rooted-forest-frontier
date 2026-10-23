import Controls
namespace Universal233.SourceCoverage.FalseControls
open RMAF CoreProgram
-- Must be rejected: original-label refinement permits homogeneous coarsening.
theorem false_exact_partition :
    CoreProgram.Controls.parts (generate CoreProgram.Controls.cherry3
      SourceCoverage.Controls.thirdParentColor 2) = [[[0],[1],[2]]] := by decide
end Universal233.SourceCoverage.FalseControls
