import RAInterface
namespace OrdinaryDispatch.RecoveryAttemptBits.Controls
open Universal233 WholeSourceWork CoreProgram
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits OrdinaryDispatch.RecoveryControlBits

def g : BitGroup:=⟨[false],[[true]],[]⟩
def h : BitGroup:=⟨[true],[[false,true]],[true]⟩
def t : BitTree:=.node [] (.leaf g) (.leaf h)
def cb : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt:=fun _ _ _=>prunedReceipt

theorem rootFirst : (attemptBits 2 cb t [] [[]] {g with origin:=[]}).value.refusals=[.rootCut] := by decide +kernel
theorem rootPaid : (attemptBits 2 cb t [] [[]] {g with origin:=[]}).work=30 := by decide +kernel
theorem duplicate : (attemptBits 2 cb t [] [[false]] g).value.refusals=[.duplicateCut] := by decide +kernel
theorem entire : (attemptBits 2 cb (.leaf g) [] [] g).value.refusals=[.entireRemoval] := by decide +kernel
theorem successful : (attemptBits 2 cb t [] [] g).value.refusals=[] := by decide +kernel
theorem prunedKept : decode (attemptBits 2 cb t [] [] g).value.pruned=1 := by decide +kernel
theorem attemptCount : decode (attemptBits 2 cb t [] [] g).value.childAttempts=1 := by decide +kernel
theorem noVisit : decode (attemptBits 2 cb t [] [] g).value.visited=0 := by decide +kernel
theorem noOutput : (attemptBits 2 cb t [] [] g).value.outputs=[] := by decide +kernel
theorem addressStructural : (attemptBits 2 cb t [] [[false,false]] g).value.refusals=[] := by decide +kernel
theorem finiteRefusal : (viewReceipt (attemptBits 2 cb t [] [[false]] g).value).refusals=["duplicate original source cut"] := by decide +kernel
theorem overflowWitness : decode (attemptBits 0 cb t [] [] g).value.childAttempts=0 := by decide +kernel
theorem copiesIdentity : (copyGroups [g,h]).value=[g,h] := by decide +kernel
theorem closesPaid : (closeGroups [g]).work+(closeArrays [[false]]).work+(closeTree (.leaf h)).work≤(attemptBits 2 cb t [] [] g).work := by decide +kernel
theorem continuationState :
 (callOwned 3 (fun next ds cs=>⟨⟨[],[],[],[],[]⟩, (closeTree next).work+(closeGroups ds).work+(closeArrays cs).work⟩) (.leaf h) [] [] g).value.childAttempts=[true] := by decide +kernel
theorem refusalCounterOne : decode (attemptBits 2 cb (.leaf g) [] [] g).value.childAttempts=1 := by decide +kernel

#check rootFirst
#check rootPaid
#check duplicate
#check entire
#check successful
#check prunedKept
#check attemptCount
#check noVisit
#check noOutput
#check addressStructural
#check finiteRefusal
#check overflowWitness
#check copiesIdentity
#check closesPaid
#check continuationState
#check refusalCounterOne
end OrdinaryDispatch.RecoveryAttemptBits.Controls
