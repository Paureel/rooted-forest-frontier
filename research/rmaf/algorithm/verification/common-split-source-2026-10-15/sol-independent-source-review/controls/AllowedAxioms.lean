import Std
namespace TrustAllowed
universe u
theorem allowedPropext (p q : Prop) (h : p ↔ q) : p = q := propext h
noncomputable def allowedChoice (α : Sort u) (h : Nonempty α) : α := Classical.choice h
theorem allowedQuot {α : Sort u} {r : α → α → Prop} {a b : α} (h : r a b) : Quot.mk r a = Quot.mk r b := Quot.sound h
end TrustAllowed
