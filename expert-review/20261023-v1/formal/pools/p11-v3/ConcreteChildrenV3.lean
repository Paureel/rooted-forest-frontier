import ForestTotalityV3

namespace SourceForestV3
open RMAF Universal233 Universal233.CherryBranching
open GenericForest GenericForest.FrontierWork
open SourceCouplingV2 SourceDisjointV2 SourceChildrenV2 SourceSelectedChildrenV2
open Universal233.Rule5SelectedLocalWork

def payload (out : Result) : SourceChildrenV2.ForestReturn := ⟨out.value,out.debit⟩

def concreteWorker (OrdExec : Tree → Tree → Nat → Option F → Prop) (mode : Mode)
    (T : Option Tree) (ss : List Tree) (q : Nat) (fr : SourceChildrenV2.ForestReturn) : Prop :=
  ∃ out, ForestExec OrdExec mode 0 T ss q out ∧ fr=payload out

variable {OrdExec : Tree → Tree → Nat → Option F → Prop} {mode : Mode}
  {base : Tree → Tree → Nat → Option F}

theorem concrete_worker_value
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (h : concreteWorker OrdExec mode T ss q fr) :
    fr.value=GenericForest.solve (ordinarySpec mode base) T ss q := by
  obtain ⟨out,execution,rfl⟩ := h
  exact (forest_correspondence sound q 0 T ss out execution).1

theorem concrete_worker_debit
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (h : concreteWorker OrdExec mode T ss q fr) :
    fr.debit=OrdinaryDispatch.WorkRecursion.forestWork (ordinarySpec mode base)
      (fun _ _ _=>0) T ss q := by
  obtain ⟨out,execution,rfl⟩ := h
  exact (forest_correspondence sound q 0 T ss out execution).2.1

theorem concrete_worker_total
    (total : ∀ T S b, enabled mode b=true → ∃ a, OrdExec T S b a)
    (T : Option Tree) (ss : List Tree) (q : Nat) : ∃ fr, concreteWorker OrdExec mode T ss q fr := by
  obtain ⟨out,execution⟩ := forest_exists total q 0 T ss
  exact ⟨payload out,out,execution,rfl⟩

variable {T S : Tree} {q a b ticks : Nat} {cs : List Child}
  {r : ForestReceipt (List SourceChildrenV2.Forest)} {debits : List Nat}

theorem concrete_children_total
    (total : ∀ T S b, enabled mode b=true → ∃ a, OrdExec T S b a)
    (T : Tree) (q : Nat) (cs : List Child) :
    ∃ r debits ticks, ChildrenRun (concreteWorker OrdExec mode) T q cs r debits ticks := by
  exact children_exists (concrete_worker_total total) T q cs

theorem concrete_children_source
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (h : ChildrenRun (concreteWorker OrdExec mode) T q cs r debits ticks) :
    finishSource T S q r debits =
      OrdinaryDispatch.FullSourceWork.runChildrenSource (ordinarySpec mode base)
        (fun _ _ _=>0) T S q cs := by
  exact finish_source_projection h
    (fun _ _ _ _ h=>concrete_worker_value sound h)
    (fun _ _ _ _ h=>concrete_worker_debit sound h)

theorem concrete_one_source
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (h : ChildrenRun (concreteWorker OrdExec mode) T q [(pendantChildMeter S a b).value] r debits ticks) :
    finishOne T S q a b r debits =
      OrdinaryDispatch.FullSourceWork.oneSource (ordinarySpec mode base)
        (fun _ _ _=>0) T S q a b := by
  exact one_source_projection h
    (fun _ _ _ _ h=>concrete_worker_value sound h)
    (fun _ _ _ _ h=>concrete_worker_debit sound h)

theorem concrete_high_source
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (h : ChildrenRun (concreteWorker OrdExec mode) T q
      (OrdinaryDispatch.FullSourceWork.branchesMeter S a b).value r debits ticks) :
    finishHigh T S q a b r debits =
      OrdinaryDispatch.FullSourceWork.highSource (ordinarySpec mode base)
        (fun _ _ _=>0) T S q a b := by
  exact high_source_projection h
    (fun _ _ _ _ h=>concrete_worker_value sound h)
    (fun _ _ _ _ h=>concrete_worker_debit sound h)

end SourceForestV3
