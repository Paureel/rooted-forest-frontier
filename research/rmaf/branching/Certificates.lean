import Std

/- Exact arithmetic certificates for c = 231/100. These do not establish
   structural branching safety, termination, or an improved rMAF algorithm.
   Multiplication clears the positive denominators in each branching sum. -/
namespace RMAFBranchingCertificates

theorem macro_a_certificate :
    2 * 231^3 * 100 + 3 * 100^4 ≤ 231^4 := by decide

theorem macro_b_certificate :
    2 * 231^4 * 100 + 231^2 * 100^3 + 2 * 100^5 ≤ 231^5 := by decide

theorem macro_c_certificate :
    2 * 231^3 * 100 + 231 * 100^3 + 100^4 ≤ 231^4 := by decide

theorem source_t3_certificate :
    2 * 231^2 * 100 + 100^3 ≤ 231^3 := by decide

theorem source_boundary_certificate :
    231 * 100 + 3 * 100^2 ≤ 231^2 := by decide

theorem source_five_branches_certificate :
    5 * 100^2 ≤ 231^2 := by decide

theorem source_split_certificate :
    2 * 100 ≤ 231 := by decide

theorem original_recurrence_fails_target :
    231^4 < 2 * 231^3 * 100 + 231 * 100^3 + 2 * 100^4 := by decide

#print axioms macro_a_certificate
#print axioms macro_b_certificate
#print axioms macro_c_certificate
#print axioms source_t3_certificate
#print axioms source_boundary_certificate
#print axioms source_five_branches_certificate
#print axioms source_split_certificate
#print axioms original_recurrence_fails_target

end RMAFBranchingCertificates
