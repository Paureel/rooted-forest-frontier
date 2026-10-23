import CommonOrientation
import CutoffFacts
import Hard2Exact
namespace OrdinaryDispatch.FastOrdinary
open RMAF ForestState Universal233 Universal233.CherryBranching

/-- Actual two-orientation ordinary recursion. The concrete sealed hard2
handler replaces the scaffold's baseline hard2 branch. No solver oracle or
proof is a runtime argument. -/
def solve (q : Nat) (T S : Tree) : Option CommonForest :=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .refused => none
  | .found c => if DepthOne.cutCost c≤q then some (DepthOne.forest S c) else none
  | .rejected =>
   let paid := fun u v r => if hr : r<q then solve r u v else none
   match early T S with
   | .common reverse c =>
     let p := commonPair T S reverse c
     if hn : (leaves p.1).length<(leaves T).length then
       (solve q p.1 p.2).map (expandCommon T S reverse c)
     else none
   | .one reverse c =>
     let p := Oriented reverse T S
     runChildren paid p.1 p.2 q [pendantChild p.2 c.a c.b]
   | .high reverse c =>
     let p := Oriented reverse T S
     runChildren paid p.1 p.2 q (branches p.2 c.a c.b)
   | .rule4Forward s => runRule4 paid s q
   | .rule4Reverse s => runRule4 paid s q
   | .hard2 c d => Hard2Dispatcher.run paid T S c d q
   | .refused => none
 else none
termination_by (q,(leaves T).length)
decreasing_by
 all_goals simp_wf
 all_goals first | exact Prod.Lex.left _ _ hr | exact Prod.Lex.right _ hn
end OrdinaryDispatch.FastOrdinary
