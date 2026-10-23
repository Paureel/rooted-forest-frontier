import Std
namespace ClassificationStandardPlant
noncomputable def select (α : Type) (h : Nonempty α) : α := Classical.choice h
theorem ext (p q : Prop) (h : p ↔ q) : p = q := propext h
theorem quotient (r : Nat → Nat → Prop) (a b : Nat) (h : r a b) :
    Quot.mk r a = Quot.mk r b := Quot.sound h
end ClassificationStandardPlant
