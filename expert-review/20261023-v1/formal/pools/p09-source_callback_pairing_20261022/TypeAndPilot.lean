import CompleteWeightedSource
import OrdinaryChildrenSource
import QueryWork

open RMAF
open OrdinaryDispatch
open GenericForest.FrontierWork

#check CompleteSource.completeSourceCounter
#check FullSourceWork.sourceSubtotal
#check CompleteSource.completeLocalDebit
#check WorkRecursion.ordinaryStepTrace
#check FastOrdinary.solve
#check FullSourceWork.runChildrenSource
#check GenericForest.solve
#check frontier
#check Universal233.Rule5OrdinaryDispatch.Child
#check Universal233.Rule5SelectedLocalWork.runChildrenMeter

namespace CallbackPairingAuthor

-- One-shot finite pilot; computational types and bodies remain canonical.
def comb : List Nat → Tree
  | [] => .leaf 0
  | [a] => .leaf a
  | a::as => .node (.leaf a) (comb as)

def samples : List Tree :=
  [comb [0,1,2,3,4,5], comb [1,3,5,0,2,4], comb [5,4,3,2,1,0],
   .node (.node (.leaf 0) (.leaf 1)) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 4) (.leaf 5))),
   .node (.node (.leaf 0) (.leaf 2)) (.node (.node (.leaf 1) (.leaf 4)) (.node (.leaf 3) (.leaf 5)))]

def pilot := samples.zipIdx |>.flatMap fun (t,i) =>
  samples.zipIdx |>.flatMap fun (s,j) =>
  [0,1,2,3].filterMap fun q =>
    let r := WorkRecursion.ordinaryStepTrace FastOrdinary.solve q t s
    if r.queries.isEmpty then none else
      some (i,j,q,r.value.isSome,r.queries.map fun p => (p.2,(leaves p.1.1).length,(leaves p.1.2).length))

#eval pilot

end CallbackPairingAuthor
