import Std
namespace PlantPrivate
private axiom hiddenPrivate : Nat
noncomputable def exposed : Nat := hiddenPrivate
end PlantPrivate
