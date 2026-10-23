import RAControls
namespace OrdinaryDispatch.RecoveryAttemptBits.Controls
open Universal233 WholeSourceWork CoreProgram
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits OrdinaryDispatch.RecoveryControlBits
example : (attemptBits 2 cb t [] [[]] {g with origin:=[]}).value.refusals=[.duplicateCut] := by decide +kernel
example : (attemptBits 2 cb t [] [[false]] g).value.refusals=[.rootCut] := by decide +kernel
example : (attemptBits 2 cb (.leaf g) [] [] g).value.refusals=[] := by decide +kernel
example : decode (attemptBits 2 cb t [] [] g).value.childAttempts=0 := by rw [attemptCount]; decide +kernel
example : decode (attemptBits 2 cb t [] [] g).value.pruned=0 := by decide +kernel
example : (attemptBits 2 cb t [] [[false,false]] g).value.refusals=[.duplicateCut] := by decide +kernel
example : decode (attemptBits 0 cb t [] [] g).value.childAttempts=1 := by decide +kernel
example : (attemptBits 2 cb t [] [] g).work=0 := by decide +kernel
end OrdinaryDispatch.RecoveryAttemptBits.Controls
