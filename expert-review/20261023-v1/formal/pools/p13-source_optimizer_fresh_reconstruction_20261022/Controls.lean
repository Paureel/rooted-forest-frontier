/- One-shot exact synthetic optimizer plumbing controls; no candidate imports. -/
namespace FreshOptimizerControls
structure Trial where
  budget : Nat
  success : Bool
  charge : Nat
  deriving DecidableEq, Repr

structure Scan where
  charge : Nat
  attempts : List Nat
  deriving DecidableEq, Repr

def scan : List Trial → Scan
  | [] => ⟨0, []⟩
  | c :: cs =>
    if c.success then ⟨c.charge, [c.budget]⟩
    else
      let tail := scan cs
      ⟨c.charge + tail.charge, c.budget :: tail.attempts⟩

structure Run where
  work : Nat
  attempts : List Nat
  recoveries : Nat
  deriving DecidableEq, Repr

def meter (preflight recovery : Nat) (cs : List Trial) : Run :=
  let r := scan cs
  ⟨preflight + r.charge + recovery, r.attempts, 1⟩

def cells : List Trial :=
  [⟨0, false, 5⟩, ⟨1, false, 11⟩, ⟨2, true, 17⟩, ⟨3, true, 101⟩]

def clean := meter 7 23 cells
example : clean = ⟨63, [0, 1, 2], 1⟩ := by decide
example : (3 - 1 : Nat) = 2 := by decide
example : (3 - 1 : Nat) + 1 = 3 := by decide
example : (233 : Nat) ^ (3 - 1) = 54289 := by decide
example : (100 : Nat) ^ (3 - 1) = 10000 := by decide
example : meter 7 23 [⟨0, true, 17⟩] = ⟨47, [0], 1⟩ := by decide
example : meter 0 0 [⟨0, false, 0⟩, ⟨1, true, 0⟩] = ⟨0, [0, 1], 1⟩ := by decide

-- Corruptions share the evaluator input path and alter only one assembly rule.
def successOnly (preflight recovery : Nat) (cs : List Trial) : Run :=
  meter preflight recovery (cs.filter (fun c => c.success))
def shiftedQ (k : Nat) := k

def repeatedRecovery (preflight recovery : Nat) (cs : List Trial) : Run :=
  let r := scan cs
  ⟨preflight + r.charge + r.attempts.length * recovery, r.attempts, r.attempts.length⟩

example : (successOnly 7 23 cells).work = 47 := by decide
example : (shiftedQ 3) + 1 = 4 := by decide
example : (repeatedRecovery 7 23 cells).work = 109 := by decide
#eval clean
end FreshOptimizerControls
