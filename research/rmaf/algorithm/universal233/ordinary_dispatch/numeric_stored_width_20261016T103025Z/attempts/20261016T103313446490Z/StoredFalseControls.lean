import StoredPrecontrols
open GenericForest.ScalarBits
example : decode (incrementBits [true,true,true]).value=0 := by decide
example : ([false,false,false,false] : List Bool).length≤1 := by decide
example : (copyBits [false,true,false]).work=0 := by decide
