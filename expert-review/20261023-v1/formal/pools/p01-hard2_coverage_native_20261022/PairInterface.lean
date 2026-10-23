import PairOptimalV3
namespace ContactedGoodPair
-- Both exact original Forest abbreviation values are List (List Nat).
-- This checks the transparent interface conversion used in stored-row binding.
theorem forest_abbrev_normal : Forest=List (List Nat) := rfl
theorem ordinary_abbrev_normal : Ordinary=(RMAF.Tree→RMAF.Tree→Nat→Option (List (List Nat))) := rfl
end ContactedGoodPair

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedGoodPair.forest_abbrev_normal
#print axioms ContactedGoodPair.forest_abbrev_normal
#check @ContactedGoodPair.ordinary_abbrev_normal
#print axioms ContactedGoodPair.ordinary_abbrev_normal
