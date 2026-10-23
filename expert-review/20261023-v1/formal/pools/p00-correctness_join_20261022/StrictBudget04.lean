-- Parametric exact spelling of requested OwnPaid/BelowBudget, no FastSolve import.
import LocalExact
import CommonDispatch
open RMAF OrdinaryDispatch
namespace HighCompletion
abbrev OrdinarySolver := Nat → Tree → Tree → Option (List (List Nat))
def OwnPaid (ordinary : OrdinarySolver) (q : Nat) : Tree → Tree → Nat → Option (List (List Nat)) :=
 fun t s b => if b<q then ordinary b t s else none
def BelowBudget (ordinary : OrdinarySolver) (q : Nat) : Prop :=
 ∀ b,b<q → ∀ T S,Universal233.DepthOne.proper T S=true → QueryExact T S b (ordinary b T S)
theorem local_ordinary_ih (ordinary : OrdinarySolver) (q r : Nat)
    (hbelow : BelowBudget ordinary q) (hr : r<q) :
    ForestMinCompletion.LocalOrdinaryIH r (OwnPaid ordinary q) := by
  constructor
  · intro t s b F hb hp hF
    have hbq : b<q := Nat.lt_of_le_of_lt hb hr
    have hcall : ordinary b t s=some F := by simpa only [OwnPaid,if_pos hbq] using hF
    have hex:=hbelow b hbq t s hp
    rw [hcall] at hex
    exact hex
  · intro t s b G hb hp hag hcost
    have hbq : b<q := Nat.lt_of_le_of_lt hb hr
    have hex:=hbelow b hbq t s hp
    cases ho : ordinary b t s with
    | none =>
      rw [ho] at hex
      exact False.elim (Nat.not_lt_of_ge hcost (hex G hag))
    | some F =>
      exact ⟨F,by simp only [OwnPaid,if_pos hbq,ho]⟩
theorem own_paid_cutoff (ordinary : OrdinarySolver) (q b : Nat) (T S : Tree) (hb : q≤b) :
    OwnPaid ordinary q T S b=none := by
  exact if_neg (Nat.not_lt_of_ge hb)
#print axioms local_ordinary_ih
end HighCompletion
