import Std
namespace PaidCoverMassChecks
-- Each statement concerns only the printed paid vector, not coverage or
-- a global runtime bound. Positive denominators have been cleared.
theorem full_cover_fails_2_31 : 231^2 < 2*231*100 + 8*100^2 := by decide
theorem full_cover_fails_benchmark :
    23391^2 < 2*23391*10000 + 8*10000^2 := by decide
theorem printed_full_cover_mass_at_four : 4^2 = 2*4 + 8 := by decide
theorem compatible_three_color_mass_passes :
    231*100^2 + 2*100^3 < 231^3 := by decide
#print axioms full_cover_fails_2_31
#print axioms full_cover_fails_benchmark
#print axioms printed_full_cover_mass_at_four
#print axioms compatible_three_color_mass_passes
end PaidCoverMassChecks
