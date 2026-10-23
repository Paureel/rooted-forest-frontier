import Std
namespace ToyGood
def answer : Nat := 7
theorem answer_ok : answer = 7 := rfl
private def privateSeed : Nat := 11
def privateProducer : Nat := privateSeed
theorem producer_ok : privateProducer = 11 := rfl
end ToyGood
