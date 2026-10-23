import Std
namespace OwnTotalRec
def count : List Nat → Nat
  | [] => 0
  | _::xs => 1 + count xs
theorem plantedTrue : count [2,4,6]=3 := by decide
end OwnTotalRec
