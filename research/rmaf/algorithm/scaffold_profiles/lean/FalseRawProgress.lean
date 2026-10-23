import Std
-- Deliberate false twin: no continuation gain is needed in the dangerous case.
theorem false_raw_progress : 2*100*233^3 + 100^3*233 + 2*100^4 ≤ 233^4 := by decide
