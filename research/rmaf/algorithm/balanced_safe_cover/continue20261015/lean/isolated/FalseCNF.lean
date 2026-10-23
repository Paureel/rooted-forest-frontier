import Std
example : ([3] : List Nat).all (fun h => ([1] : List Nat).any (fun g => Nat.land g h == g)) = false := by
  decide
