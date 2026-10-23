import RIControls
open OrdinaryDispatch.RecoveryInitialBits OrdinaryDispatch.RecoveryInitialBits.Controls OrdinaryDispatch.RecoveryBits
example : (initializeBits 10 dup [[o]] big).value≠none := by
 rw [show (initializeBits 10 dup [[o]] big).value=none from by decide +kernel];decide
example : (initializeBits 10 paddedDup [[o]] big).value≠none := by
 rw [show (initializeBits 10 paddedDup [[o]] big).value=none from by decide +kernel];decide
example : summary (initializeBits 10 tri forest big).value=some (1000,expected) := by
 rw [show summary (initializeBits 10 tri forest big).value=some (2,expected) from by decide +kernel];decide
example : decode (ownedColor forest tw).value=2 := by rw [ownedColor_value];decide
example : (appendAddress [true,false] true).value=[true,false,false] := by rw [appendAddress_value];decide
example : (leafArrays tri).value=[z,tw,o] := by rw [leafArrays_value];decide
example : (copyInput (.leaf sev)).work=16 := by decide
example : (closeBits sev).work=12 := by decide
example : (ownedEqual sev sev).work=87 := by
 rw [show (ownedEqual sev sev).work=88 from by decide +kernel];decide
example : (summary (initializeBits 2 four [[z],[o],[tw],[th]] th).value).map Prod.fst=some 3 := by
 rw [show (summary (initializeBits 2 four [[z],[o],[tw],[th]] th).value).map Prod.fst=some 0 from by decide +kernel];decide
example : (normalizeBits same).value=same := by
 rw [show (normalizeBits same).value=sameNorm from by decide +kernel];decide
example : (normalizeBits expected).value=expected := by
 rw [show (normalizeBits expected).value=expectedNorm from by decide +kernel];decide
