import ToyGood
namespace ToyGenerated
inductive Cell where
  | empty
  | cell (value : Nat)
def read : Cell → Nat
  | .empty => 0
  | .cell n => n
theorem read_cell : read (.cell 19) = 19 := rfl
end ToyGenerated
