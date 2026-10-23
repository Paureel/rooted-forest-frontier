import CommonDispatch
import CherryDispatch
namespace OrdinaryScaffold
open RMAF ForestState Universal233 Universal233.CherryBranching OrdinaryDispatch

/-- Executable scaffold, with the original three-branch hard2 rule. It carries
no claim of the target improved exponential base. -/
def solve (q : Nat) (T S : Tree) : Option (List (List Nat)) :=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .refused => none
  | .found c => if DepthOne.cutCost c≤q then some (DepthOne.forest S c) else none
  | .rejected =>
   let paid := fun u v r => if hr : r<q then solve r u v else none
   match select T S with
   | none => none
   | some (.common,c) =>
    let z := commonFresh T
    let t := contract c.a c.b z T
    let s := contract c.a c.b z S
    if hn : (leaves t).length<(leaves T).length then
     (solve q t s).map (fun F=>F.map (expandBlock c.a c.b z))
    else none
   | some (.one,c) => runChildren paid T S q [pendantChild S c.a c.b]
   | some (.high,c) => runChildren paid T S q (branches S c.a c.b)
   | some (.hard2,c) => runChildren paid T S q (branches S c.a c.b)
 else none
termination_by (q,(leaves T).length)
decreasing_by
 all_goals simp_wf
 all_goals first | exact Prod.Lex.left _ _ hr | exact Prod.Lex.right _ hn

end OrdinaryScaffold
