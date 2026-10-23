import PersistentEntry
open GenericForest.BinaryProvider
example : (containsLabel [true] [[true,false]]).value=false := by decide +kernel
