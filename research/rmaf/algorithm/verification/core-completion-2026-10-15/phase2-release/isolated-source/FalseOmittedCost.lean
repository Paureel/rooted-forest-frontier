import RationalMass
open Universal233.CoreProgram Universal233.SourceCoverage
example : (generate Controls.crossed Controls.parity 3).outputs.length = 2 := by decide +kernel
example : (Controls.costs (generate Controls.crossed Controls.parity 3)).all (fun c => decide (2 ≤ c)) = true := by decide +kernel
example : (combine (generate Controls.crossed Controls.parity 3) (generate Controls.crossed Controls.parity 3)).outputs.length = 4 := by decide +kernel
def refines (fine coarse : List (List Nat)) : Bool := fine.all (fun b => coarse.any (fun a => b.all a.contains))
example : refines [[0],[1],[2]] [[0,1],[2]] = true := by decide +kernel
def os := (generate Controls.crossed Controls.parity 2).outputs
def duplicated := [os.getD 0 ⟨[],[]⟩,os.getD 0 ⟨[],[]⟩,os.getD 1 ⟨[],[]⟩]
example : (duplicated.map (fun o => o.sourceCuts.length)).sum = 6 := by decide +kernel
example : rawQMass 2 duplicated = 3/4 := by decide +kernel
example : rawQMass (233/100) duplicated = 30000/54289 := by decide +kernel

example : (duplicated.map (fun o => o.sourceCuts.length)).sum = 4 := by decide +kernel
