import ScalarPrecontrols
open GenericForest.ScalarBits.Controls
example : decode [true,false,true]=6 := by decide
example : (31:Nat)+1=0 := by decide
example : (32:Nat)-1=32 := by decide
example : (1:Nat)-32=31 := by decide
