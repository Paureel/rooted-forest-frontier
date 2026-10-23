import GroupPriority

/-! One-shot literal ordinary-restriction materializer for current source output.
Missing restrictions are filtered operationally; checked nonempty Q proves that
none is missing. No default tree or assumed graph/cost field is used. -/
namespace OutputState
open RMAF RestrictionBridge ForestState

def sourceForest (S : Tree) (Q : List (List Nat)) : List Tree :=
  Q.filterMap (fun U => restrict U S)

end OutputState
