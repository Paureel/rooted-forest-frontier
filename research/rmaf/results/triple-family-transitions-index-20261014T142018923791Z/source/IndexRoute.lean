import FamilyAssembly

/-! One-shot independent finite-index supporting proof for family merge.
Only the old FamilyAssembly semantics are shared. No geometry constructor is
asserted. -/
namespace TripleDP.CostRoute.IndexRoute

variable {I J : Type}

/-- Enumerate the actual surviving indices; the proof field forbids the removed
member from even inhabiting the retained type. -/
def survivors [DecidableEq I] (o : I) : List I → List {x : I // x ≠ o}
  | [] => []
  | x :: xs => if h : x = o then survivors o xs else ⟨x, h⟩ :: survivors o xs

/-- Left/right constructors keep even equal-looking child names distinct. -/
inductive Joined (o : I) (p : J) where
  | boundary : Joined o p
  | left : {x : I // x ≠ o} → Joined o p
  | right : {y : J // y ≠ p} → Joined o p
  deriving DecidableEq

def enumeration [DecidableEq I] [DecidableEq J]
    (xs : List I) (ys : List J) (o : I) (p : J) : List (Joined o p) :=
  .boundary :: ((survivors o xs).map Joined.left ++ (survivors p ys).map Joined.right)

def closedEnumeration [DecidableEq I] [DecidableEq J]
    (xs : List I) (ys : List J) (o : I) (p : J) : List (Joined o p) :=
  (survivors o xs).map Joined.left ++ (survivors p ys).map Joined.right

def singletonEnums := enumeration ([0] : List Nat) ([0] : List Nat) 0 0

def singletonClosed := closedEnumeration ([0] : List Nat) ([0] : List Nat) 0 0

def collisionLeft : Joined (0 : Nat) (0 : Nat) := .left ⟨1, by decide⟩
def collisionRight : Joined (0 : Nat) (0 : Nat) := .right ⟨1, by decide⟩

example : singletonEnums.length = 1 := by decide
example : singletonClosed.length = 0 := by decide
example : collisionLeft ≠ collisionRight := by decide

end TripleDP.CostRoute.IndexRoute
