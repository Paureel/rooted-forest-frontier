import ProducerBudgetTrim
namespace OrdinaryDispatch.StoredNumeric.ProducerBinding.Controls
open GenericForest.ScalarBits GenericForest.BinaryProvider
example : (trimBudget [false,false,false,false]).value=[] ∧ (trimBudget [false,false,false,false]).work=33 := by decide
example : (subtractCanonical [true] [false,true]).value=[] := by cbv
example : (trimBudget (incrementBits [true,true,true]).value).value=[false,false,false,true] := by cbv
example : (trimBudget [true,false,true,false,false]).value=[true,false,true] := by decide
example : (trimBudget (List.replicate 1024 false)).work=8193 := by decide
example : (trimBudget (List.replicate 1024 false)).value=[] := by decide
example : (allocationCanonical [false,false,false,true,false,false] [false,true] [false,true]).value=[false,false,true] := by cbv
example : ([false,false,false,false] : Bits).length>decode [false,false,false,false] := by decide
end OrdinaryDispatch.StoredNumeric.ProducerBinding.Controls
