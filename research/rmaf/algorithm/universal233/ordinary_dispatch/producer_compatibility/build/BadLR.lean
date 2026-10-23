import LeftValue
import RightValue
open ProducerPlant
-- Instrument plant only. Record whether the module importer itself rejects
-- incompatible definitions or whether the stored producer audit must do so.
theorem incompatible_import_false : False := by
  have h : (0 : Nat) = 1 := left.symm.trans right
  cases h
#print axioms incompatible_import_false
