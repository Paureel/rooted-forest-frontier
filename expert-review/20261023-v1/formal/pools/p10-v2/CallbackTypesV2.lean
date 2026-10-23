import LocalCreditV2
open RMAF ForestState GenericForest GenericForest.FrontierWork
open Universal233.PaidQueries SourceCouplingV2
set_option pp.fullNames true
#check pairCallback
#print GenericForest.FrontierWork.pairCallback
example (f : Tree → Tree → Nat → Option (List (List Nat))) :
    pairCallback f = (fun p b => (f p.1 p.2 b).map (fun F=>(F.length-1,F))) := by
  rfl
