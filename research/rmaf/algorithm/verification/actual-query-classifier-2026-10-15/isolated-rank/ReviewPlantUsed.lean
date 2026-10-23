import Std
namespace QueryClassifierToyUsed
private axiom freeQueries : (2 : Nat) = 0
private theorem hiddenBill : (2 : Nat) = 0 := freeQueries
theorem publicBill : (2 : Nat) = 0 := hiddenBill
end QueryClassifierToyUsed
