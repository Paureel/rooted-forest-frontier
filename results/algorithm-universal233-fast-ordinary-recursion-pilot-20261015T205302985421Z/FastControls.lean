import FastExact
import Hard2Plant
namespace OrdinaryDispatch.FastOrdinary.Controls
open RMAF ForestState Universal233 Universal233.CherryBranching Rule5Local.Pre
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

def runtimeChecks : List (String×Bool) :=
 [("quartet_negative",solve 1 quartetT quartetS==none),
  ("quartet_three_blocks",(solve 2 quartetT quartetS).map (fun F => (agreement quartetT quartetS F,F.length))==some (true,3)),
  ("same_zero",(solve 0 quartetT quartetT).map (fun F => (agreement quartetT quartetT F,F.length))==some (true,1)),
  ("malformed",solve 2 (.leaf 0) (.leaf 1)==none),
  ("common_expand",(solve 2 graftT graftS).map (fun F => (agreement graftT graftS F,F.length))==some (true,3)),
  ("reverse_three_blocks",(solve 2 quartetS quartetT).map (fun F => (agreement quartetS quartetT F,F.length))==some (true,3)),
  ("external_kzero",(external quartetT quartetS 0).isNone),
  ("external_kone",(external quartetT quartetS 1).isNone),
  ("external_ktwo",(external quartetT quartetS 2).isNone),
  ("external_kthree",(external quartetT quartetS 3).map (fun o => (agreement quartetT quartetS o.partition,o.partition.length,o.sourceCuts.length))==some (true,3,2)),
  ("hard2_budget_two",(solve 2 sixT sixS).isNone),
  ("hard2_budget_three",(solve 3 sixT sixS).map (fun F => (agreement sixT sixS F,F.length))==some (true,4))]
#eval runtimeChecks
#eval ("PASS_ACTUAL_TOTAL_RECURSION_CONTROLS",runtimeChecks.all Prod.snd)
#eval ("actual_hard2_budgets",(List.range 4).map fun q => (q,(solve q sixT sixS).map List.length))
end OrdinaryDispatch.FastOrdinary.Controls
