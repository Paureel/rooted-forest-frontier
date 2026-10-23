import BinaryCallerActual
import CallerPrecontrols
namespace GenericForest.BinaryCaller.Controls
open GenericForest.BinaryProvider GenericForest.ScalarBits

def F : BinaryProvider.Forest:=[[a],[b]]
def paddedF : BinaryProvider.Forest:=[[[true,false]],[b]]
def badF : BinaryProvider.Forest:=[[],[a],[b]]
def xs : List (Nat×BinaryProvider.Forest):=[(0,[[],[a]]),(1,[[b]])]

theorem optional_truth : (checkOptional (some pair) [pair] q8 none).value=none ∧
 (checkOptional (some pair) [pair] q8 none).work=1 ∧
 (checkOptional (some pair) [pair] q8 (some F)).value=some F := by decide +kernel

theorem flatten_truth : (flattenAnswers xs).value=badF ∧ (flattenAnswers xs).work=23 ∧
 (disjointFinish pair [pair] q8 (some xs)).value=none := by decide +kernel

theorem raw_truth : (bestCandidates (some pair) [pair] q8 [badF,paddedF,F]).value=some paddedF ∧
 (bestCandidates (some pair) [pair] q8 [badF,badF]).value=none := by decide +kernel

theorem duplicate_setup_truth :
 setupCallsWork (some pair) [pair] q8 [badF,badF]=2*(checkerCapacity (some pair) [pair] q8 badF).work ∧
 0<(checkerCapacity (some pair) [pair] q8 badF).work ∧
 setupCallsWork (some pair) [pair] q8 [badF,badF]≤(bestCandidates (some pair) [pair] q8 [badF,badF]).work := by decide +kernel

theorem payment_truth : decode (payBudget q8 [(),(),()]).value=5 ∧
 (payBudget q8 [(),(),()]).value.length=4 ∧ 2<decode (payBudget q8 [(),(),()]).value := by decide +kernel

theorem original_bound_truth : 4≤(checkerCapacity (some pair) [pair] q8 badF).value.length ∧
 (checkerCapacity (some pair) [pair] q8 badF).value.length≤2+8+2*3+3 := by decide +kernel
end GenericForest.BinaryCaller.Controls
