import MarkInteraction
open PureBridgeMarks
-- Deliberately false: both individually free marks remain jointly free.
example : optimum [markV,markW] = some 1 := by decide
