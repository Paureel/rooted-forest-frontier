import Std
namespace SolPrivate
private axiom hidden : Nat
noncomputable def generated : Nat → Nat
  | 0 => hidden
  | n + 1 => generated n
theorem clean : True := True.intro
end SolPrivate
