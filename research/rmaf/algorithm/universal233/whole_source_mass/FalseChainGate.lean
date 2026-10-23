import MassControls
open RMAF VertexGeometry Universal233.SourceCoverage Universal233.WholeSourceMass
open Universal233.WholeSourceMass.MassControls
theorem false_count_two_rank_five :
  5 ≤ (dedupNat ((leaves chain).map
    (taggedColor ca cb (fun _ => 0) (jointLabel chain [false] [true]) (fun _ => 0)))).length := by decide
