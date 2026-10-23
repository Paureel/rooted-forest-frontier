import RAInterface
namespace OrdinaryDispatch.RecoveryAttemptBits.Controls
open Universal233 WholeSourceWork CoreProgram
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits OrdinaryDispatch.RecoveryControlBits

def g : BitGroup:=⟨[false],[[true]],[]⟩
def h : BitGroup:=⟨[true],[[false,true]],[true]⟩
def t : BitTree:=.node [] (.leaf g) (.leaf h)
def cb : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt:=fun _ _ _=>prunedReceipt

theorem rootFirst : (attemptBits 2 cb t [] [[]] {g with origin:=[]}).value.refusals=[.rootCut] := by decide
theorem rootPaid : (attemptBits 2 cb t [] [[]] {g with origin:=[]}).work=30 := by decide
theorem duplicate : (attemptBits 2 cb t [] [[false]] g).value.refusals=[.duplicateCut] := by decide
theorem entire : (attemptBits 2 cb (.leaf g) [] [] g).value.refusals=[.entireRemoval] := by decide
theorem successful : (attemptBits 2 cb t [] [] g).value.refusals=[] := by decide
theorem prunedKept : decode (attemptBits 2 cb t [] [] g).value.pruned=1 := by decide
theorem attemptCount : decode (attemptBits 2 cb t [] [] g).value.childAttempts=1 := by decide
theorem noVisit : decode (attemptBits 2 cb t [] [] g).value.visited=0 := by decide
theorem noOutput : (attemptBits 2 cb t [] [] g).value.outputs=[] := by decide
theorem addressStructural : (attemptBits 2 cb t [] [[false,false]] g).value.refusals=[] := by decide
theorem finiteRefusal : (viewReceipt (attemptBits 2 cb t [] [[false]] g).value).refusals=["duplicate original source cut"] := by decide
theorem overflowWitness : decode (attemptBits 0 cb t [] [] g).value.childAttempts=0 := by decide
theorem copiesIdentity : (copyGroups [g,h]).value=[g,h] := by decide
theorem closesPaid : (closeGroups [g]).work+(closeArrays [[false]]).work+(closeTree (.leaf h)).work≤(attemptBits 2 cb t [] [] g).work := by decide
theorem continuationState :
 (callOwned 3 (fun next ds cs=>⟨⟨[],[],[],[],[]⟩, (closeTree next).work+(closeGroups ds).work+(closeArrays cs).work⟩) (.leaf h) [] [] g).value.childAttempts=[true] := by decide
theorem refusalCounterOne : decode (attemptBits 2 cb (.leaf g) [] [] g).value.childAttempts=1 := by decide

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
#guard_msgs in
example : (attemptBits 2 cb t [] [[]] {g with origin:=[]}).value.refusals=[.duplicateCut] := by decide
#guard_msgs in
example : (attemptBits 2 cb t [] [[false]] g).value.refusals=[.rootCut] := by decide
#guard_msgs in
example : (attemptBits 2 cb (.leaf g) [] [] g).value.refusals=[] := by decide
#guard_msgs in
example : decode (attemptBits 2 cb t [] [] g).value.childAttempts=0 := by decide
#guard_msgs in
example : decode (attemptBits 2 cb t [] [] g).value.pruned=0 := by decide
#guard_msgs in
example : (attemptBits 2 cb t [] [[false,false]] g).value.refusals=[.duplicateCut] := by decide
#guard_msgs in
example : decode (attemptBits 0 cb t [] [] g).value.childAttempts=1 := by decide
#guard_msgs in
example : (attemptBits 2 cb t [] [] g).work=0 := by decide
end OrdinaryDispatch.RecoveryAttemptBits.Controls
