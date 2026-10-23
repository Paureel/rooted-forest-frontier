import ForestSingletonV2

namespace SourceSelectedChildrenV2
open RMAF Universal233 Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FullSourceWork
open Universal233.Rule5SelectedLocalWork SourceChildrenV2

def finishOne (T S : Tree) (q a b : Nat)
    (r : ForestReceipt (List SourceChildrenV2.Forest)) (debits : List Nat) :
    WholeSourceWork.Charged (Option (List (List Nat))) :=
  let c := pendantChildMeter S a b
  let z := finishSource T S q r debits
  ⟨z.value,c.work+z.work+2⟩

def finishHigh (T S : Tree) (q a b : Nat)
    (r : ForestReceipt (List SourceChildrenV2.Forest)) (debits : List Nat) :
    WholeSourceWork.Charged (Option (List (List Nat))) :=
  let c := branchesMeter S a b
  let z := finishSource T S q r debits
  ⟨z.value,c.work+z.work+2⟩

theorem one_source_projection
    (h : ChildrenRun FExec T q [(pendantChildMeter S a b).value] r debits ticks)
    (soundValue : ∀ t ss b fr, FExec t ss b fr →
      fr.value = GenericForest.solve actual t ss b)
    (soundDebit : ∀ t ss b fr, FExec t ss b fr →
      fr.debit = WorkRecursion.forestWork actual (fun _ _ _=>0) t ss b) :
    finishOne T S q a b r debits = oneSource actual (fun _ _ _=>0) T S q a b := by
  have hs := finish_source_projection (S:=S) h soundValue soundDebit
  simp only [finishOne,oneSource,hs]

theorem high_source_projection
    (h : ChildrenRun FExec T q (branchesMeter S a b).value r debits ticks)
    (soundValue : ∀ t ss b fr, FExec t ss b fr →
      fr.value = GenericForest.solve actual t ss b)
    (soundDebit : ∀ t ss b fr, FExec t ss b fr →
      fr.debit = WorkRecursion.forestWork actual (fun _ _ _=>0) t ss b) :
    finishHigh T S q a b r debits = highSource actual (fun _ _ _=>0) T S q a b := by
  have hs := finish_source_projection (S:=S) h soundValue soundDebit
  simp only [finishHigh,highSource,hs]

end SourceSelectedChildrenV2
