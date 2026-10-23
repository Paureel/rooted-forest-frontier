import SourceCompression
open ScaffoldProfiles.Source RMAF
-- A monochromatic two-color partition is not automatically an agreement forest.
theorem false_terminal : agreement exchangeTarget exchangeSource [[0,1],[2,3],[4,5]] = true := by decide
