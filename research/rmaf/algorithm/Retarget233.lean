import Std

/-! Arithmetic at a versioned alternative base 233/100. The structural chain
core, coverage, generation and complete-algorithm obligations are OPEN. -/
namespace RMAFAlgorithmRetarget233

theorem paid_four_two_chain_passes :
    2 * 233^3 * 100 + 4 * 100^4 ≤ 233^4 := by decide

theorem paid_four_two_chain_fails_231 :
    231^4 < 2 * 231^3 * 100 + 4 * 100^4 := by decide

theorem unreplaced_bottleneck_fails_233 :
    233^4 < 2 * 233^3 * 100 + 233 * 100^3 + 2 * 100^4 := by decide

theorem strict_smaller_than_benchmark :
    233 * 10000 < 23391 * 100 := by decide

#print axioms paid_four_two_chain_passes
#print axioms paid_four_two_chain_fails_231
#print axioms unreplaced_bottleneck_fails_233
#print axioms strict_smaller_than_benchmark

end RMAFAlgorithmRetarget233
