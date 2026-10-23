import RCStorage
namespace OrdinaryDispatch.RecoveryAttemptBits
open Universal233 WholeSourceWork CoreProgram
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits OrdinaryDispatch.RecoveryControlBits

inductive RefusalTag where
 | empty | homogeneous | noCherry | rootCut | duplicateCut | entireRemoval | duplicateLabel
 deriving DecidableEq,Repr
/-- Specification interpretation only; runtime stores a finite constructor tag. -/
def viewRefusal : RefusalTag→String
 | .empty=>"empty current source"
 | .homogeneous=>"unnormalized homogeneous cherry"
 | .noCherry=>"no mixed cherry in multicolor source"
 | .rootCut=>"attempt to cut original root"
 | .duplicateCut=>"duplicate original source cut"
 | .entireRemoval=>"attempt removed entire current source"
 | .duplicateLabel=>"duplicate original label"
structure BitReceipt where
 outputs : List BitOutput
 refusals : List RefusalTag
 visited : List Bool
 childAttempts : List Bool
 pruned : List Bool
 deriving DecidableEq,Repr
/-- Specification only. No represented producer calls this function. -/
def viewReceipt (r : BitReceipt) : Receipt :=
 ⟨r.outputs.map viewOutput,r.refusals.map viewRefusal,decode r.visited,decode r.childAttempts,decode r.pruned⟩
def ReceiptWords (C : Nat) (r : BitReceipt) : Prop :=
 r.visited.length≤C ∧ r.childAttempts.length≤C ∧ r.pruned.length≤C

/-- Literal allocation: empty outputs 2, singleton tag 4, two empty counters 4,
one-bit counter 6, receipt constructor 8. -/
def refusalReceipt (tag : RefusalTag) : Charged BitReceipt :=
 ⟨⟨[],[tag],[],[true],[]⟩,2+4+2+6+2+8⟩
@[simp] theorem refusalReceipt_value (tag : RefusalTag) :
 viewReceipt (refusalReceipt tag).value=⟨[],[viewRefusal tag],0,1,0⟩ := rfl
@[simp] theorem refusalReceipt_work (tag : RefusalTag) : (refusalReceipt tag).work=24 := rfl
theorem refusalReceipt_words (C : Nat) (positive : 1≤C) (tag : RefusalTag) :
 ReceiptWords C (refusalReceipt tag).value := by simp [ReceiptWords,refusalReceipt];omega
/-- Actual zero-fuel callback retains a pruned event and no visited/attempt event. -/
def prunedReceipt : Charged BitReceipt := ⟨⟨[],[],[],[],[true]⟩,2+2+2+2+6+8⟩
@[simp] theorem prunedReceipt_value : viewReceipt prunedReceipt.value=⟨[],[],0,0,1⟩ := rfl
@[simp] theorem prunedReceipt_work : prunedReceipt.work=22 := rfl

/-- Consumes the old child counter through stepLength's explicit old/raw closes;
other receipt fields transfer unchanged. The eight units cover record destructure
and reconstruction. No output/refusal list is traversed or discarded here. -/
def bumpAttempt (C : Nat) (r : BitReceipt) : Charged BitReceipt :=
 let a:=stepLength C r.childAttempts
 ⟨{r with childAttempts:=a.value},a.work+8⟩
theorem bumpAttempt_value (C : Nat) (r : BitReceipt)
 (fits : decode r.childAttempts+1<2^C) :
 viewReceipt (bumpAttempt C r).value={viewReceipt r with childAttempts:=(viewReceipt r).childAttempts+1} := by
 simp only [bumpAttempt,viewReceipt,stepLength_value C _ fits]
theorem bumpAttempt_work (C : Nat) (r : BitReceipt) (words : r.childAttempts.length≤C) :
 (bumpAttempt C r).work≤72*(C+1) := by
 have a:=stepLength_work C r.childAttempts words
 simp only [bumpAttempt];omega
theorem bumpAttempt_words (C : Nat) (r : BitReceipt) (words : ReceiptWords C r) :
 ReceiptWords C (bumpAttempt C r).value := ⟨words.1,stepLength_length C _,words.2.2⟩
theorem bumpAttempt_lifetime (C : Nat) (r : BitReceipt) :
 (closeBits (addCarry true r.childAttempts []).value).work+(closeBits r.childAttempts).work≤(bumpAttempt C r).work := by
 simp only [bumpAttempt,stepLength];omega
end OrdinaryDispatch.RecoveryAttemptBits
