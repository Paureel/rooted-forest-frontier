import RationalMass
namespace Universal233.SourceCoverage.Probe
example : (2 : Rat) ≤ mkRat 233 100 := by decide
example : (2 : Rat) ≤ (233 : Rat) / 100 := by grind [Rat.div_def]
example : (2 : Rat) * (mkRat 100 233) ^ 2 ≤ mkRat 100 233 := by decide
end Universal233.SourceCoverage.Probe
