import Std

/- Literal CB3 projected-child cost profiles on the original six-leaf star
   fixture. This is a finite arithmetic obstruction to the specified uniform
   recurrence; graph extraction is retained separately in the Python receipt. -/
namespace AllRowObstruction

def profiles : List (Nat × List Nat) := [
 (29,[1,1,1,1]), (109,[1,1,1,1,3]), (117,[1,1,1,1,3]),
 (121,[1,1,1,1,3]), (124,[1,1,1,1,3]),
 (429,[1,1,1,1,1,3]), (437,[1,1,1,1,1,3]),
 (441,[1,1,1,1,1,3]), (444,[1,1,1,1,1,3]),
 (693,[1,1,1,1,3]), (697,[1,1,1,1,3]), (700,[1,1,1,1,3]),
 (709,[1,1,1,1]), (732,[1,1,1,1,1]),
 (745,[1,1,1,1,3]), (748,[1,1,1,1,3]), (752,[1,1,1,3]),
 (773,[1,1,1,1]), (796,[1,1,1,1,1]),
 (873,[1,1,1,1,1,3]), (876,[1,1,1,1,1,3]),
 (880,[1,1,1,1,3]), (937,[1,1,1,1,3]), (940,[1,1,1,1,3]),
 (944,[1,1,1,3]), (960,[1,1,1])
]

def numerator343 (deltas : List Nat) : Nat :=
  (deltas.map (fun d => 3 ^ d * 7 ^ (3 - d))).sum

theorem profileCount : profiles.length = 26 := by decide

theorem everyRowHasThreeUnitChildren :
    ∀ p ∈ profiles, 3 ≤ p.2.count 1 := by decide

theorem everySevenThirdsMassAtLeastNineSevenths :
    ∀ p ∈ profiles, 441 ≤ numerator343 p.2 := by decide

theorem bestSevenThirdsMassAttained : numerator343 [1,1,1] = 441 := by decide

theorem nineSeventhsExceedsOne : 441 > 343 := by decide

theorem unitMassObstruction (numerator denominator units : Nat)
    (three : 3 ≤ units) (subThree : numerator < 3 * denominator) :
    numerator < units * denominator := by
  exact Nat.lt_of_lt_of_le subThree (Nat.mul_le_mul_right denominator three)

theorem versionedAlternativeBelowBenchmark : 7 * 10000 < 3 * 23391 := by decide

#print axioms profileCount
#print axioms everyRowHasThreeUnitChildren
#print axioms everySevenThirdsMassAtLeastNineSevenths
#print axioms bestSevenThirdsMassAttained
#print axioms nineSeventhsExceedsOne
#print axioms unitMassObstruction
#print axioms versionedAlternativeBelowBenchmark

end AllRowObstruction
