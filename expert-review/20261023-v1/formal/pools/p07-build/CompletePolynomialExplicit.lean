import CompleteWeightedSource
namespace OrdinaryDispatch.CompleteSource
open RMAF Universal233
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.OuterSource

/-- Fixed polynomial expression; no counter, residual fee or target work oracle. -/
theorem completeSourcePolynomial_explicit (N Q L : Nat) :
 completeSourcePolynomial N Q L=outerJoinedPolynomial N Q L+
 (disjointRunPolynomial (2*N+3)+badPairLocalPolynomialExpression (2*N+3) Q+
 32*(2^50*((2*N+3)+Q+2)^8)) := by
 unfold completeSourcePolynomial residualPolynomialNat
 rw [badPairLocalPolynomial_explicit]

/-- The final source optimizer contains its original source recovery once.
This coefficient has no asserted relation to the finite recovery coefficient. -/
theorem completeOptimizeCoefficient_explicit (n L : Nat) :
 completeOptimizeCoefficient n L=
 n*(completeSourcePolynomial n n L*1024*(n+1))+512*(2*n+1)^2+
 OrdinaryDispatch.RecoveryLocalWork.recoverySourceEnvelope n := rfl
end OrdinaryDispatch.CompleteSource
