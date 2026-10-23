import Std
def refines (fine coarse : List (List Nat)) : Bool := fine.all (fun b => coarse.any (fun a => b.all a.contains))
example : refines [[0,1],[2]] [[0],[1],[2]] = true := by decide
