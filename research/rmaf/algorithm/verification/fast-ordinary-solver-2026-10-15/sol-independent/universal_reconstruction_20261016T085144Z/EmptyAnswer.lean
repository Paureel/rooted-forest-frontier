/- Deliberately wrong accepted forest; must be rejected by coverage. -/
import ReconstructionV2
open RMAF Universal233 OrdinaryDispatch IndependentReconstruction
example : QueryExact (.leaf 0) (.leaf 0) 0 (some []) := by
  refine ⟨?_,by decide,?_⟩
  · decide
  · intro F hF
    simp
