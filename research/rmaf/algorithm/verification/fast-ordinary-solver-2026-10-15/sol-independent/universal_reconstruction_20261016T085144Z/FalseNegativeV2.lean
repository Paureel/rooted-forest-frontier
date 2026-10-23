/- Deliberately wrong negative-answer claim; must be rejected. -/
import ReconstructionV2
open RMAF Universal233 OrdinaryDispatch IndependentReconstruction
example : QueryExact (.leaf 0) (.leaf 0) 0 none := by
  change ∀ F,agreement (.leaf 0) (.leaf 0) F=true → 0<F.length-1
  intro F hF
  have positive := agreement_positive hF
  omega
