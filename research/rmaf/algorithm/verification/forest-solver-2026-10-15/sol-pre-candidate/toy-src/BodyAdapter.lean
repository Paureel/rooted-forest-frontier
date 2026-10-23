import Std
namespace GateToy
private def producer : List Nat → Nat
  | [] => 0
  | x :: xs => x + producer xs

def exported (xs : List Nat) : Nat := producer xs

def publicPayload : Nat := 8

theorem checked : exported [2,3] = 5 := by decide

private def ignored (xs : List (Option Nat)) : Nat :=
  match xs with
  | [] => 11
  | some n :: _ => n
  | none :: ys => ignored ys

def unusedProducer : Nat := ignored [none, some 19]
end GateToy
