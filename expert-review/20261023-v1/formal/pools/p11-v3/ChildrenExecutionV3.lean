import ConcreteChildrenV3

namespace SourceForestV3
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5SelectedLocalWork
open GenericForest GenericForest.FrontierWork
open SourceCouplingV2 SourceDisjointV2 SourceChildrenV2
open CallbackPairingAuthor (indexFrom)

def indexedWorker (OrdExec : Tree → Tree → Nat → Option F → Prop) (mode : Mode)
    (T : Option Tree) (ss : List Tree) (q : Nat) (fr : SourceChildrenV2.ForestReturn) : Prop :=
  ∃ k out, ForestExec OrdExec mode k T ss q out ∧ fr=payload out

inductive ChildrenExec (OrdExec : Tree → Tree → Nat → Option F → Prop)
    (mode : Mode) (T : Tree) (q : Nat) :
    Nat → List Child → ForestReceipt (List F) → List Nat → List S → Prop
  | nil : ChildrenExec OrdExec mode T q k [] ⟨[],1,0,[]⟩ [] []
  | refused (over : ¬c.paid≤q)
      (tail : ChildrenExec OrdExec mode T q k cs r debits slots) :
      ChildrenExec OrdExec mode T q k (c::cs) (prependChild ⟨none,2,0,[]⟩ r) debits slots
  | returned (paid : c.paid≤q)
      (execution : ForestExec OrdExec mode k (some T) c.sourceForest (q-c.paid) out)
      (tail : ChildrenExec OrdExec mode T q (k+out.slots.length) cs r debits slots) :
      ChildrenExec OrdExec mode T q k (c::cs)
        (prependChild ⟨out.value,4,0,[⟨c,q-c.paid⟩]⟩ r)
        (out.debit::debits) (out.slots++slots)

variable {OrdExec : Tree → Tree → Nat → Option F → Prop} {mode : Mode}
  {base : Tree → Tree → Nat → Option F}

theorem indexed_worker_value
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (h : indexedWorker OrdExec mode T ss q fr) :
    fr.value=GenericForest.solve (ordinarySpec mode base) T ss q := by
  obtain ⟨k,out,execution,rfl⟩ := h
  exact (forest_correspondence sound q k T ss out execution).1

theorem indexed_worker_debit
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (h : indexedWorker OrdExec mode T ss q fr) :
    fr.debit=OrdinaryDispatch.WorkRecursion.forestWork (ordinarySpec mode base)
      (fun _ _ _=>0) T ss q := by
  obtain ⟨k,out,execution,rfl⟩ := h
  exact (forest_correspondence sound q k T ss out execution).2.1

theorem children_forget
    (h : ChildrenExec OrdExec mode T q k cs r debits slots) :
    ∃ ticks, ChildrenRun (indexedWorker OrdExec mode) T q cs r debits ticks := by
  induction h with
  | nil => exact ⟨_,ChildrenRun.nil⟩
  | refused over tail ih =>
    obtain ⟨ticks,ht⟩ := ih
    exact ⟨_,ChildrenRun.cons (ChildRun.refused over) ht⟩
  | returned paid execution tail ih =>
    obtain ⟨ticks,ht⟩ := ih
    have hw : indexedWorker OrdExec mode _ _ _ _ := ⟨_,_,execution,rfl⟩
    exact ⟨_,ChildrenRun.cons (ChildRun.returned paid hw) ht⟩

def childrenQueries (actual : GenericForest.FrontierWork.Ordinary)
    (T : Tree) (q : Nat) (cs : List Child) : List Q :=
  (Rule5OrdinaryDispatch.forestJobs T q cs).flatMap fun j=>frontier actual j.target j.sources j.residual

theorem children_index
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (h : ChildrenExec OrdExec mode T q k cs r debits slots) :
    slots.map (fun s=>(s.index,s.query))=indexFrom k (childrenQueries (ordinarySpec mode base) T q cs) := by
  induction h with
  | nil => rfl
  | refused over tail ih =>
    simpa [childrenQueries,Rule5OrdinaryDispatch.forestJobs,
      Rule5OrdinaryDispatch.jobFor,remaining,over] using ih
  | returned paid execution tail ih =>
    have hq := (forest_correspondence sound _ _ _ _ _ execution).2.2
    have hl := index_length hq
    rw [List.map_append,hq,ih,hl,←indexFrom_append]
    congr 1
    simp [childrenQueries,Rule5OrdinaryDispatch.forestJobs,
      Rule5OrdinaryDispatch.jobFor,remaining,paid]

theorem children_execution_exists
    (total : ∀ T S b, enabled mode b=true → ∃ a, OrdExec T S b a)
    (T : Tree) (q k : Nat) (cs : List Child) :
    ∃ r debits slots, ChildrenExec OrdExec mode T q k cs r debits slots := by
  induction cs generalizing k with
  | nil => exact ⟨_,_,_,ChildrenExec.nil⟩
  | cons c cs ih =>
    by_cases paid : c.paid≤q
    · obtain ⟨out,execution⟩ := forest_exists total (q-c.paid) k (some T) c.sourceForest
      obtain ⟨r,debits,slots,tail⟩ := ih (k+out.slots.length)
      exact ⟨_,_,_,ChildrenExec.returned paid execution tail⟩
    · obtain ⟨r,debits,slots,tail⟩ := ih k
      exact ⟨_,_,_,ChildrenExec.refused paid tail⟩

theorem children_source_fields
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (h : ChildrenExec OrdExec mode T q k cs r debits slots) (right : Tree) :
    finishSource T right q r debits =
      OrdinaryDispatch.FullSourceWork.runChildrenSource (ordinarySpec mode base)
        (fun _ _ _=>0) T right q cs := by
  obtain ⟨ticks,ht⟩ := children_forget h
  exact finish_source_projection ht
    (fun _ _ _ _ h=>indexed_worker_value sound h)
    (fun _ _ _ _ h=>indexed_worker_debit sound h)

end SourceForestV3
