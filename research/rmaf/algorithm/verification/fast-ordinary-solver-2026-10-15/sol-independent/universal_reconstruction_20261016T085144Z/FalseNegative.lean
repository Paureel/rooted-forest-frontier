/- Deliberately wrong negative-answer claim; must be rejected. -/
import ReconstructionV2
open RMAF Universal233 OrdinaryDispatch IndependentReconstruction
example : QueryExact (.leaf 0) (.leaf 0) 0 none := by
  intro F hF
  have positive := agreement_positive hF
  omega
