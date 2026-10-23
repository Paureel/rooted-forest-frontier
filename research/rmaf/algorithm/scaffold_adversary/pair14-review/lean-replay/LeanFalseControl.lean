import Lean

-- Deliberately false: this module must fail to compile under the released toolchain.
theorem pair14_false_arithmetic_control : (2 + 2 : Nat) = 5 := by decide
