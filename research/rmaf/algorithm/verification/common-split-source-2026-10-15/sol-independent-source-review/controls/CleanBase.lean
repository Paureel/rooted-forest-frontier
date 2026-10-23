import Std
namespace ProducerControl
theorem shared : True := True.intro
theorem own : 0 = 0 := rfl
private theorem hidden : True := True.intro
def seven : Nat := 7
inductive Mini where
  | a
  | b
end ProducerControl
