import FiniteSelection

namespace TripleDP.Transitions.Restriction
open TripleDP.CostRoute

variable {α I : Type} {l r : BTree α}

def child (l r : BTree α) : Bool → BTree α
  | false => l
  | true => r

def Live (A : Family (.node l r) I) (side : Bool) (i : I) : Prop :=
  ∃ a x, LeafAt (child l r side) a x ∧ A.support i (side :: a)

abbrev LiveIndex (A : Family (.node l r) I) (side : Bool) :=
  {i // Live A side i}

def OpenBranchLive (A : Family (.node l r) I) : Prop :=
  ∀ o, A.boundary = some o → ∀ side,
    (∃ a, A.support o (side :: a)) → Live A side o

#print axioms child
#print axioms Live
#print axioms OpenBranchLive
end TripleDP.Transitions.Restriction
