import ClassifierRequestMeter
namespace Universal233.ClassifierCheckFee
open Rule5PendantLocalWork

theorem request_size_polynomial (N : Nat) : requestSize N+1=2*N*N+2*N+2 := by
 simp only [requestSize,payloadCap,Nat.mul_assoc,Nat.mul_left_comm N 2]
 omega

/-- Explicit degree-ten uniform Kc polynomial in the existing inspection units. -/
theorem check_cap_polynomial (N : Nat) :
 checkCap N=120*(2*N*N+2*N+2)^5+128*(N+1)^2 := by
 unfold checkCap
 rw [request_size_polynomial]

end Universal233.ClassifierCheckFee
