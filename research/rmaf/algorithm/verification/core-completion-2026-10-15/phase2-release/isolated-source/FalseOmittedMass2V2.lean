import RationalMass
open Universal233.CoreProgram Universal233.SourceCoverage
def actual := (generate Controls.crossed Controls.parity 2).outputs
def duplicated := [actual.getD 0 ⟨[],[]⟩,actual.getD 0 ⟨[],[]⟩,actual.getD 1 ⟨[],[]⟩]
theorem cleanMass2 : rawQMass 2 duplicated = mkRat 3 4 := by decide +kernel
theorem cleanMass233 : rawQMass (233/100) duplicated = mkRat 30000 54289 := by decide +kernel

example : rawQMass 2 duplicated = 1/2 := by
  rw [cleanMass2]
  change mkRat 3 4 = mkRat 1 2
  decide
