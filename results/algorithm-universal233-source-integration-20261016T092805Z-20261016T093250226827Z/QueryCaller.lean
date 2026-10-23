import Lean

namespace Universal233.PaidQueries

inductive Job (P A : Type) where
  | resolved (problem : P) (cost : Nat) (answer : A)
  | hard (problem : P)
  deriving Repr

def Job.problem : Job P A → P
  | .resolved p _ _ => p
  | .hard p => p

def knownCost : List (Job P A) → Nat
  | [] => 0
  | .resolved _ c _ :: js => c + knownCost js
  | .hard _ :: js => knownCost js

def pending : List (Job P A) → Nat
  | [] => 0
  | .resolved _ _ _ :: js => pending js
  | .hard _ :: js => 1 + pending js

def answerCost (xs : List (Nat × A)) : Nat := (xs.map Prod.fst).sum

structure Receipt (A : Type) where
  answers : Option (List (Nat × A))
  calls : List Nat
  visits : Nat
  deriving Repr

def run (solve : P → Nat → Option (Nat × A)) (b : Nat) : List (Job P A) → Receipt A
  | [] => ⟨some [], [], 0⟩
  | .resolved _ c a :: js =>
    let r := run solve b js
    ⟨r.answers.map ((c,a) :: ·), r.calls, r.visits+1⟩
  | .hard p :: js =>
    match solve p b with
    | none => ⟨none, [b], 1⟩
    | some x =>
      let r := run solve b js
      ⟨r.answers.map (x :: ·), b :: r.calls, r.visits+1⟩

def allocated (q : Nat) (js : List (Job P A)) : Nat :=
  q - knownCost js - 2*(pending js-1)

def schedule (solve : P → Nat → Option (Nat × A)) (q : Nat)
    (js : List (Job P A)) : Receipt A :=
  if q < knownCost js + 2*pending js then ⟨none, [], 0⟩ else
    let r := run solve (allocated q js) js
    ⟨r.answers.bind (fun xs => if answerCost xs ≤ q then some xs else none),
      r.calls, r.visits⟩

private theorem private_origin_control : 2+2=4 := by decide
theorem exported_origin_control : 2+2=4 := private_origin_control
end Universal233.PaidQueries
