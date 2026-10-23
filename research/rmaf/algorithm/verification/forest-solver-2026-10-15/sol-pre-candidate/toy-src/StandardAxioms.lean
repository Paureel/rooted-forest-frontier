import Std
namespace StandardToy

theorem ext (p q : Prop) (h : p ↔ q) : p = q := propext h

noncomputable def chosen (α : Type) (h : Nonempty α) : α := Classical.choice h

theorem quotientSound {α : Sort u} (r : α → α → Prop) (a b : α) (h : r a b) :
    Quot.mk r a = Quot.mk r b := Quot.sound h

end StandardToy
