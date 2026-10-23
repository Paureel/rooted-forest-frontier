import RightValue
import LeftValue
open ProducerPlant
theorem incompatible_import_false : False := by
  have h : (0 : Nat) = 1 := left.symm.trans right
  cases h
#print axioms incompatible_import_false
