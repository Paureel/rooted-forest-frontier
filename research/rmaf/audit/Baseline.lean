import Std

/- Arithmetic only: denominators cleared for the published [1,1,3,4,4]
   branch vector. This does not formalize the structural branching proof. -/
namespace RMAFBaselineAudit
theorem reported_base_covers_vector :
    2 * 23391^3 * 10000 + 23391 * 10000^3 + 2 * 10000^4 ≤ 23391^4 := by decide
theorem rounded_down_base_fails_vector :
    2339^4 < 2 * 2339^3 * 1000 + 2339 * 1000^3 + 2 * 1000^4 := by decide
theorem cuts_to_components (k : Nat) (hk : 1 ≤ k) : k - 1 + 1 = k := by omega
#print axioms reported_base_covers_vector
#print axioms rounded_down_base_fails_vector
#print axioms cuts_to_components
end RMAFBaselineAudit
