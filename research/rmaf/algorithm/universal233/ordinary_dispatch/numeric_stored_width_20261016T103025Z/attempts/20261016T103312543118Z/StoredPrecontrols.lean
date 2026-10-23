import BinaryProducerSource
import CommonDispatch
import BuildSetup
namespace OrdinaryDispatch.StoredNumeric
open GenericForest.ScalarBits
example : decode [true,true,true]+1=8 := by decide
example : (incrementBits [true,true,true]).value=[false,false,false,true] := by decide
example : decode [false,false,false,false]=0 ∧ ([false,false,false,false] : List Bool).length=4 := by decide
example : (copyBits [false,true,false]).value=[false,true,false] ∧ (copyBits [false,true,false]).work=13 := by decide
example : (compareBits [false,true] [true,false]).value=.greater := by decide
end OrdinaryDispatch.StoredNumeric
