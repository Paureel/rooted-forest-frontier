import Controls
namespace Universal233.SourceCoverage.FalseControls
open CoreProgram SourceCoverage.Controls
-- Must be rejected: map/sum counts both literal list entries.
theorem false_deduplicated_mass : scaledMass 2 1 [repeatedOutput,repeatedOutput] = 1 := by decide
end Universal233.SourceCoverage.FalseControls
