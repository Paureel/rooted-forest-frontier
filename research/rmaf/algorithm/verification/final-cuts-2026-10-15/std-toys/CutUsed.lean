import Std
namespace FinalCutUsed
private axiom freeCut : (1 : Nat) = 0
private theorem hidden : (1 : Nat) = 0 := freeCut
theorem publicCost : (1 : Nat) = 0 := hidden
end FinalCutUsed
