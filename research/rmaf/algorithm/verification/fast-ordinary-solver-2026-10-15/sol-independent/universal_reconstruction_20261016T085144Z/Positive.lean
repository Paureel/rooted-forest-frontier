import ReconstructionV2
open RMAF Universal233 OrdinaryDispatch IndependentReconstruction
example (a q : Nat) : QueryExact (.leaf a) (.leaf a) q (some [[a]]) := by
  refine ⟨?_,by simp,?_⟩
  · simp [agreement,leaves,partitionCheck,restrictionAgrees,restrict,sameShape,pairwiseEmbeddings]
  · intro F hF
    have pos := agreement_positive hF
    simpa using pos
example (valid : Nat→Bool) (xs : List Nat) (h : valid 0=true) :
  best id valid (0::xs)=some 0 := best_zero_head id valid 0 xs h rfl
