import Std
-- Mutation: erase the no-sibling-cuts premise. Must fail.
example : (((!true) && true) || ((!true) && true)) = true := by decide
