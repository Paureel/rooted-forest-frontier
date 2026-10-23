import RawMass
namespace Universal233.SourceCoverage.Probe
example : (2 : Rat) * ((100 : Rat) / 233) ^ 2 ≤ (100 : Rat) / 233 := by decide
example (x y z : Rat) : (x * y) * z = x * (y * z) := by grind
example (x y : Rat) (h : x ≤ y) : x * (1/2) ≤ y * (1/2) := by grind
end Universal233.SourceCoverage.Probe
