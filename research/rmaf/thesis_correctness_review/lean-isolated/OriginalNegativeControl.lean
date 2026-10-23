import Std
/- Deliberately false exchange-cardinality plant. This file MUST fail.
Dropping the condition that at least one path edge is removed would allow
base=0, added=1, removed=0, restored=0, whose claimed cost is 1 ≤ 0. -/
example : 0 + 1 - 0 + 0 ≤ (0 : Nat) := by decide
