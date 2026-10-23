import Std
namespace ToyStandard
theorem propextUse (p q : Prop) (h : p ↔ q) : p = q := propext h
theorem choiceUse (p : Prop) (h : p) : p := Classical.choice (show Nonempty p from ⟨h⟩)
theorem quotUse (r : Nat → Nat → Prop) (a b : Nat) (h : r a b) :
    Quot.mk r a = Quot.mk r b := Quot.sound h
end ToyStandard
