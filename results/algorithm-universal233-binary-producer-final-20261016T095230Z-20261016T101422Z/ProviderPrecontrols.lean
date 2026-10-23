import PolynomialBitBound
namespace GenericForest.BinaryProvider.Controls
open GenericForest.ScalarBits

def a : List Bool := [true,false,true]
def paddedA : List Bool := [true,false,true,false,false]
theorem supplied_array_truth : (copiedEqual a paddedA).value=true ∧
 ScalarBits.decode a=5 ∧ (copyBits a).value=a ∧ (copyBits a).work=13 := by decide +kernel
theorem supplied_counter_truth : ScalarBits.decode (addBits [true,true,true] [true]).value=8 ∧
 ScalarBits.decode (subtractBits [true] [false,false,true]).value=0 ∧
 (indexBits 4 [4,5,6] [false,true]).value=some 6 := by decide +kernel
end GenericForest.BinaryProvider.Controls
