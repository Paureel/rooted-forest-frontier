import GroupedControls
namespace Universal233.GroupedFullQuery.Controls
open RMAF ForestState ForestGroups RestrictionBridge PaidQueries
example : allocated 5 twoHard=4 := by decide
example : allocated 3 jobs=3 := by decide
example : (schedule planted 3 ([.hard pAB] : List (Job Problem Forest))).answers=
 some [(2,[[99]]),(1,cAnswer)] := by decide
example : actualQueryMass 2 3 (schedule planted 3 ([.hard pAB] : List (Job Problem Forest))).calls≤(1/2 : Rat) := by rw [sole_mass];decide +kernel
end Universal233.GroupedFullQuery.Controls
