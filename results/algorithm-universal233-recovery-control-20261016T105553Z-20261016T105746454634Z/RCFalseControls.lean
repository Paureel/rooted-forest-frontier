import RCControls
open OrdinaryDispatch.RecoveryControlBits OrdinaryDispatch.RecoveryControlBits.Controls OrdinaryDispatch.RecoveryBits
example : (chooseBits 8 (.leaf g0)).value=.one g0 := by
 rw [show (chooseBits 8 (.leaf g0)).value=.finish from by decide +kernel];decide
example : (chooseBits 8 two).value=.two g0 g1 := by
 rw [show (chooseBits 8 two).value=.one g0 from by decide +kernel];decide
example : (chooseBits 8 quartet).value=.one g0 := by
 rw [show (chooseBits 8 quartet).value=.two g0 g1 from by decide +kernel];decide
example : (chooseBits 8 homogeneousFirst).value=.two g0 hom1 := by
 rw [show (chooseBits 8 homogeneousFirst).value=.refuse .homogeneousCherry from by decide +kernel];decide
example : (findUnique 8 late late).value=some g0 := by
 rw [show (findUnique 8 late late).value=some g3 from by decide +kernel];decide
example : (mixedBits quartet).value=some (g2,g3) := by
 rw [show (mixedBits quartet).value=some (g0,g1) from by decide +kernel];decide
example : (chooseBits 8 padded).value=.one g0 := by
 rw [show (chooseBits 8 padded).value=.finish from by decide +kernel];decide
example : (uniqueTest 2 (List.replicate 5 g0) g0).value=false := by
 rw [show (uniqueTest 2 (List.replicate 5 g0) g0).value=true from by decide +kernel];decide
example : (copyGroup g0).work=28 := by decide
example : (closeGroups [g0]).work=34 := by decide
example : (pickPair (some (g2,g3)) (some (g0,g1))).work=85 := by decide
example : (ownedAddressEqual [] [false]).value=true := by rw [ownedAddressEqual_value];decide
example : (eraseBits [] quartet).value=some quartet := by
 rw [show (eraseBits [] quartet).value=none from by decide +kernel];decide
example : (eraseBits [false,false] two).value=some (.leaf g0) := by
 rw [show (eraseBits [false,false] two).value=some (.leaf g1) from by decide +kernel];decide
example : (eraseBits [true,true,true] quartet).value=none := by
 rw [show (eraseBits [true,true,true] quartet).value=some quartet from by decide +kernel];decide
example : (prepare 8 homogeneousFirst).value.2=.two merged0 merged1 := by
 rw [show (prepare 8 homogeneousFirst).value.2=.one merged0 from by decide +kernel];decide
