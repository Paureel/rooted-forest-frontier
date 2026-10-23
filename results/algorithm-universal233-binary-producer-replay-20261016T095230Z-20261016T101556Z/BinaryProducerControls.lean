import BinaryProducerRaw
namespace GenericForest.BinaryProducer.Controls
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork
abbrev a : Bits:=[true]
abbrev b : Bits:=[false,true]
abbrev q8 : Bits:=[false,false,false,true]
abbrev pair : BinaryProvider.Tree:=.node (.leaf a) (.leaf b)
def ok (_ : Unit) (_ : Bits) : Charged (Option (Bits×Nat)):=⟨some ([true],7),23⟩
def free (_ : Unit) (_ : Bits) : Charged (Option (Bits×Nat)):=⟨some ([true],7),0⟩
def fail (_ : Unit) (_ : Bits) : Charged (Option (Bits×Nat)):=⟨none,29⟩
def dup : List (Job Unit Nat):=[.resolved () [true] 9,.resolved () [true,false] 9,.hard ()]

theorem scheduler_truth :
 (receiptValue id (scheduleBits ok q8 dup).value).answers=some [(1,9),(1,9),(1,7)] ∧
 (receiptValue id (scheduleBits ok q8 dup).value).calls=[6] ∧
 (receiptValue id (scheduleBits ok q8 dup).value).visits=3 := by decide +kernel

theorem threshold_truth :
 (receiptValue id (scheduleBits ok [true] dup).value).answers=none ∧
 (receiptValue id (scheduleBits ok [true] dup).value).calls=[] ∧
 (receiptValue id (scheduleBits ok [true] dup).value).visits=0 := by decide +kernel

theorem failure_truth :
 (receiptValue id (runBits fail q8 [.resolved () [] 1,.hard (),.resolved () [true] 2]).value).answers=none ∧
 (receiptValue id (runBits fail q8 [.resolved () [] 1,.hard (),.resolved () [true] 2]).value).calls=[8] ∧
 (receiptValue id (runBits fail q8 [.resolved () [] 1,.hard (),.resolved () [true] 2]).value).visits=2 := by decide +kernel

theorem callback_paid_truth :
 (runBits ok q8 [.hard (),.hard ()]).work=(runBits free q8 [.hard (),.hard ()]).work+46 := by decide +kernel

def expensive (_ : Unit) (_ : Bits) : Charged (Option (Bits×Nat)):=⟨some ([true,false,false,true],7),31⟩
theorem final_reject_truth :
 (receiptValue id (scheduleBits expensive q8 [.hard ()]).value).answers=none ∧
 (receiptValue id (scheduleBits expensive q8 [.hard ()]).value).calls=[8] ∧
 (receiptValue id (scheduleBits expensive q8 [.hard ()]).value).visits=1 := by decide +kernel

theorem pretest_truth :
 (pretestBits pair pair).value=.found none ∧
 (pretestBits (.leaf a) (.leaf b)).value=.refused := by decide +kernel

def noOrdinary (_ _ : BinaryProvider.Tree) (_ : Bits) : Charged (Option BinaryProvider.Forest):=⟨none,100000⟩
theorem disjoint_truth :
 (disjointProducer noOrdinary pair [.leaf a,.leaf b] q8).value=some [[a],[b]] ∧
 (disjointProducer noOrdinary pair [.leaf a,.leaf b] q8).work<100000 := by decide +kernel

theorem source_truth :
 (sourceForestBits pair [[],[a],[b],[a]]).value=[.leaf a,.leaf b,.leaf a] ∧
 (replaceBits [[a],[b]] [false,false] [pair]).value=[.leaf a,.leaf b] ∧
 (replaceBits [[a],[b]] [false,true] [pair]).value=[pair] := by decide +kernel

def budgetAnswer (_ : Option BinaryProvider.Tree) (_ : List BinaryProvider.Tree) (q : Bits) : Charged (Option BinaryProvider.Forest):=⟨some [[q]],37⟩
def o : Output:=⟨[[a],[b]],[[false]]⟩
def zeroCut : Output:=⟨[],[]⟩
def tooMany : Output:=⟨[],List.replicate 9 [false]⟩
def rawInput : List (Bits×Output):=[([],zeroCut),([],o),([],o),([],tooMany)]
theorem raw_truth :
 ((rawCandidates budgetAnswer (some pair) [pair] q8 rawInput).value.map forestValue)=[[[7]],[[7]]] ∧
 (rawCandidates budgetAnswer (some pair) [pair] q8 rawInput).value.length=2 ∧
 (rawParentProducer budgetAnswer (some pair) [pair] q8 rawInput).value=none := by decide +kernel

theorem capacity_truth :
 (allocationBits q8 (knownBits dup).value (pendingBits dup).value).value.length≤9 ∧
 (checkerCapacity (some pair) [.leaf a,.leaf b] q8 [[a],[b]]).value.length≥4 := by decide +kernel
end GenericForest.BinaryProducer.Controls
