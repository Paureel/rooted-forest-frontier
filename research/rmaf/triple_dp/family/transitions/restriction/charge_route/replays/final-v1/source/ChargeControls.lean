import ChargeConsumer
namespace TripleDP.RestrictionCharge.Controls
open TripleDP.CostRoute

example : closedCharge [0,1] (fun _ => true) (none : Option Nat) = 2 := by decide
example : closedCharge [0,1] (fun i => i == 0) (some 0) = 0 := by decide
example : closedCharge [0,1] (fun i => i == 1) (some 1) = 0 := by decide
example : weight [0,1] (fun i => i == 0) + weight [0,1] (fun i => i == 1) = 2 := by decide
example : closedCharge [0] (fun _ => true) (some 0) = 0 := by decide
example : weight [0] (fun _ => true) + weight [0] (fun _ => true) = 1 + duplicate (fun _ => true) (fun _ => true) (some (0 : Nat)) := by decide
example : closedCharge [0,1,2] (fun _ => true) (none : Option Nat) = 3 := by decide
example : closedCharge [0,1,2] (fun i => i < 2) (none : Option Nat) = 2 := by decide
example : closedCharge [0,1,2] (fun i => i == 2) (some 2) = 0 := by decide
example : closedCharge [0,1,2] (fun _ => true) (some 0) = 2 := by decide
example : closedCharge [0,1,2] (fun i => i != 2) (some 0) = 1 := by decide
example : closedCharge [0,1,2] (fun i => i != 1) (some 0) = 1 := by decide
example : weight [0,1,2] (fun i => i != 2) = 2 := by decide
example : weight [0,1,2] (fun i => i != 2) + weight [0,1,2] (fun i => i != 1) = 4 := by decide
example : weight ([] : List Nat) (fun _ => true) = 0 := by decide
example : closedCharge ([] : List Nat) (fun _ => true) none = 0 := by decide

def two : FiniteIndex Bool where
  elems := [false,true]
  nodup := by decide
  complete := by intro i; cases i <;> simp

example : weight two.elems Bool.not + weight two.elems id = two.elems.length := by
  have h := count_balance two Bool.not id none (by intro i; cases i <;> simp)
    (by intro i hl hr; cases i <;> simp_all)
  simpa [duplicate] using h

example : closedCharge two.elems (fun _ => true) none =
    closedCharge two.elems Bool.not (some false) + closedCharge two.elems id (some true) + 1 + 1 := by
  have h := four_charges two Bool.not id none (some false) (some true)
    (by intro i; cases i <;> simp)
    (by intro i hl hr; cases i <;> simp_all)
    (by intro o h; cases o <;> simp_all)
    (by intro o h; cases o <;> simp_all)
  exact h.1 rfl

end TripleDP.RestrictionCharge.Controls
