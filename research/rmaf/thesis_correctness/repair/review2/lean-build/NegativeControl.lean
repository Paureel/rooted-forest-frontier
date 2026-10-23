import OriginalEdges
open RootSafeOriginalEdges
-- Intentionally false: no phantom LCA parent may be inserted at a root.
example : normalize [4,5,6] (fun e : Nat => e == 4 || e == 6 || e == 7) none = [3,5] := by decide
