import Std
namespace PlantBodyOnly
axiom hiddenValue : Nat
noncomputable def value : Nat := hiddenValue
noncomputable def chain : Nat := value
end PlantBodyOnly
