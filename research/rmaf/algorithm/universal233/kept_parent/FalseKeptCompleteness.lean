import KeptControls
open RMAF Universal233.CoreProgram
theorem false_every_partition_emitted : [[0],[1],[2],[3]] ∈ Controls.parts
  (generate Controls.crossed Controls.parity 3) := by decide
