import Std
namespace Case322Private
private axiom hidden : Nat
noncomputable def generated : Nat → Nat
 | 0 => hidden
 | n+1 => generated n
theorem clean : True := True.intro
end Case322Private
