import PersistentEntry
namespace GenericForest.BinaryCaller.Controls
open GenericForest.BinaryProvider GenericForest.ScalarBits
def a : Bits:=[true]
def b : Bits:=[false,true]
def q8 : Bits:=[false,false,false,true]
def pair : Tree:=.node (.leaf a) (.leaf b)
theorem above_reduced_n : decode q8=8 ∧ (leavesBits pair).length=2 ∧
 (checkerFromInput (some pair) [pair] q8 [[a],[b]]).value=some [[a],[b]] ∧
 4≤(checkerCapacity (some pair) [pair] q8 [[a],[b]]).value.length := by decide +kernel
end GenericForest.BinaryCaller.Controls
