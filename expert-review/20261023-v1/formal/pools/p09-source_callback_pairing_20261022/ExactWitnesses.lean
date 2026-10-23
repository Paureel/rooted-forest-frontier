import CompleteWeightedSource
import OrdinaryChildrenSource
import QueryWork

open RMAF
open OrdinaryDispatch
open GenericForest.FrontierWork
open Universal233.PaidQueries

namespace CallbackPairingAuthor

def t : Tree := .node (.leaf 0) (.node (.leaf 1) (.leaf 2))
def s : Tree := .node (.leaf 1) (.node (.leaf 0) (.leaf 2))
def paid : Ordinary := FastOrdinary.cutoff FastOrdinary.solve 2
def c : Universal233.CherryBranching.Child := ⟨[[0,1,2]],[s],0⟩

#check Universal233.CherryBranching.Child

-- Universal SOURCE one-step recurrence, proved from defining equations only.
theorem counter_step (q : Nat) (T S : Tree) :
  CompleteSource.completeSourceCounter q T S =
    CompleteSource.completeLocalDebit T S q +
    (((WorkRecursion.ordinaryStepTrace FastOrdinary.solve q T S).queries.attach).map
      (fun pb => CompleteSource.completeSourceCounter pb.val.2 pb.val.1.1 pb.val.1.2)).sum := by
  change FullSourceWork.sourceSubtotal CompleteSource.completeLocalDebit q T S = _
  rw [FullSourceWork.sourceSubtotal]
  rfl

-- Exact compiled counterexample to erasing work when equal-budget value refuses.
#eval (FastOrdinary.solve 2 t s, paid t s 2,
  frontier paid (some t) [s] 2,
  WorkRecursion.forestWork paid (fun _ _ _ => 0) (some t) [s] 2,
  WorkRecursion.forestWork paid (fun _ _ _ => 17) (some t) [s] 2,
  CompleteSource.completeSourceCounter 2 t s)

#eval let a := FullSourceWork.runChildrenSource paid (fun _ _ _ => 0) t s 2 [c]
      let b := FullSourceWork.runChildrenSource paid (fun _ _ _ => 17) t s 2 [c]
      (a,b)

-- Exact scheduler slots: duplicates remain two; failure retains only its prefix slot.
#eval let js : List (Job Nat Nat) := [.hard 4,.hard 4]
      let r := meterSchedule (fun p _ => some (0,p)) (fun _ _ => 7) 4 js
      (r.value.answers,r.queries,r.recursiveWork)
#eval let js : List (Job Nat Nat) := [.hard 4,.hard 4]
      let r := meterSchedule (fun _ _ => none) (fun _ _ => 7) 4 js
      (r.value.answers,r.queries,r.recursiveWork)
#eval let js : List (Job Nat Nat) := [.hard 4]
      let r := meterSchedule (fun _ _ => none) (fun _ _ => 7) 2 js
      (r.value.answers,r.queries,r.recursiveWork)

end CallbackPairingAuthor
