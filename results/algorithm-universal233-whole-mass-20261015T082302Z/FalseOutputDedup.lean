import MassControls
open Universal233.SourceCoverage
theorem false_output_dedup : rawQMass 2 [⟨[],[[]]⟩,⟨[],[[]]⟩] = (1/2 : Rat) := by
  rw [Universal233.WholeSourceMass.MassControls.raw_list_multiplicity]
  decide
