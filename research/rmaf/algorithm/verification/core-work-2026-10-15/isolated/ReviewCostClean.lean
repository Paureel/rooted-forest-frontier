import ReviewCostBridgeV4
import Controls
open RMAF Universal233.CoreProgram Universal233.CoreWork
namespace ReviewSourceUnit
 def comb : Nat → Tree | 0 => .leaf 0 | n+1 => .node (comb n) (.leaf (n+1))
 theorem helper_literal : groupsWork (fromTree id [] (comb 7)) = 79 := by decide
 theorem source_minimum : (15+8+2*28+7 : Nat) = 86 := by decide
 theorem wide_literal : reviewWideSheet 1 0 0 = 491 := by decide
 theorem wide_prune : reviewWideEnvelope 0 256 = 266 := by decide
 #print axioms helper_literal
 #print axioms source_minimum
 #print axioms wide_literal
 #print axioms wide_prune
end ReviewSourceUnit
