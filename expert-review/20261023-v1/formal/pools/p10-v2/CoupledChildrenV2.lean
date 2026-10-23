import OrdinaryChildrenSource
import SchedulerExistenceV2

namespace SourceChildrenV2
open RMAF Universal233 Universal233.CherryBranching
open Universal233.Rule5SelectedLocalWork
open OrdinaryDispatch

abbrev Forest := List (List Nat)

structure ForestReturn where
  value : Option Forest
  debit : Nat

-- FExec denotes one concrete local forest execution; its implementation is a
-- separate premise, explicitly not a table/function supplying a desired debit.
inductive ChildRun (FExec : Option Tree → List Tree → Nat → ForestReturn → Prop)
    (T : Tree) (q : Nat) : Child → ForestReceipt (Option Forest) → Nat → Nat → Prop
  | refused (over : ¬ c.paid≤q) :
      ChildRun FExec T q c ⟨none,2,0,[]⟩ 0 16
  | returned (paid : c.paid≤q)
      (execution : FExec (some T) c.sourceForest (q-c.paid) fr) :
      ChildRun FExec T q c ⟨fr.value,4,0,[⟨c,q-c.paid⟩]⟩ fr.debit 32

def prependChild (a : ForestReceipt (Option Forest)) (r : ForestReceipt (List Forest)) :
    ForestReceipt (List Forest) :=
  ⟨match a.value with | none=>r.value | some F=>F::r.value,
    a.localWork+r.localWork+a.calls.length+3,
    a.recursiveWork+r.recursiveWork,a.calls++r.calls⟩

inductive ChildrenRun (FExec : Option Tree → List Tree → Nat → ForestReturn → Prop)
    (T : Tree) (q : Nat) : List Child → ForestReceipt (List Forest) → List Nat → Nat → Prop
  | nil : ChildrenRun FExec T q [] ⟨[],1,0,[]⟩ [] 8
  | cons (head : ChildRun FExec T q c a debit headTicks)
      (tail : ChildrenRun FExec T q cs r debits tailTicks) :
      ChildrenRun FExec T q (c::cs) (prependChild a r)
        (if a.calls.isEmpty then debits else debit::debits) (headTicks+tailTicks+24)

variable {FExec : Option Tree → List Tree → Nat → ForestReturn → Prop}
  {actual : GenericForest.FrontierWork.Ordinary}
  {T S : Tree} {q : Nat} {c : Child} {cs : List Child}
  {a : ForestReceipt (Option Forest)} {r : ForestReceipt (List Forest)}
  {debit headTicks ticks : Nat} {debits : List Nat}

theorem child_projection (h : ChildRun FExec T q c a debit headTicks)
    (soundValue : ∀ t ss b fr, FExec t ss b fr →
      fr.value = GenericForest.solve actual t ss b) :
    a = childExecutionMeter actual (fun _=>0) T q c := by
  cases h with
  | refused over => simp [childExecutionMeter,over]
  | returned paid execution =>
    have hv := soundValue _ _ _ _ execution
    simp [childExecutionMeter,paid,hv]

theorem children_projection (h : ChildrenRun FExec T q cs r debits ticks)
    (soundValue : ∀ t ss b fr, FExec t ss b fr →
      fr.value = GenericForest.solve actual t ss b) :
    r = childrenAnswersMeter actual (fun _=>0) T q cs := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    have ha := child_projection head soundValue
    simp only [childrenAnswersMeter,prependChild,ha,ih]
    rfl

def queryJob (T : Tree) (call : ForestQuery) : Rule5OrdinaryDispatch.ForestJob :=
  ⟨call.child,some T,call.child.sourceForest,call.budget⟩

theorem children_jobs (h : ChildrenRun FExec T q cs r debits ticks) :
    r.calls.map (queryJob T) = Rule5OrdinaryDispatch.forestJobs T q cs := by
  induction h with
  | nil => rfl
  | @cons cc aa dd ht ccs rr ds tt head tail ih =>
    cases head with
    | refused over =>
      simpa [prependChild,Rule5OrdinaryDispatch.forestJobs,
        Rule5OrdinaryDispatch.jobFor,remaining,over] using ih
    | returned paid execution =>
      simpa [prependChild,Rule5OrdinaryDispatch.forestJobs,
        Rule5OrdinaryDispatch.jobFor,remaining,paid,queryJob] using
          congrArg (List.cons (queryJob T ⟨cc,q-cc.paid⟩)) ih

theorem children_debit (h : ChildrenRun FExec T q cs r debits ticks)
    (soundDebit : ∀ t ss b fr, FExec t ss b fr →
      fr.debit = WorkRecursion.forestWork actual (fun _ _ _=>0) t ss b) :
    debits.sum = FullSourceWork.childForestDebit actual (fun _ _ _=>0) T q cs := by
  induction h with
  | nil => rfl
  | @cons cc aa dd ht ccs rr ds tt head tail ih =>
    cases head with
    | refused over =>
      simpa [FullSourceWork.childForestDebit,Rule5OrdinaryDispatch.forestJobs,
        Rule5OrdinaryDispatch.jobFor,remaining,over] using ih
    | returned paid execution =>
      have hd := soundDebit _ _ _ _ execution
      simpa [FullSourceWork.childForestDebit,Rule5OrdinaryDispatch.forestJobs,
        Rule5OrdinaryDispatch.jobFor,remaining,paid,hd] using
          congrArg (Nat.add (WorkRecursion.forestWork actual (fun _ _ _=>0)
            (some T) cc.sourceForest (q-cc.paid))) ih

theorem children_debit_count (h : ChildrenRun FExec T q cs r debits ticks) :
    debits.length = r.calls.length := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | refused over => simpa [prependChild] using ih
    | returned paid execution => simpa [prependChild] using congrArg Nat.succ ih

-- Closed local source computation; agreement work is computed from the literal
-- agreementMeter expression, not an externally supplied agreement fee.
def finishChildren (T S : Tree) (q : Nat) (r : ForestReceipt (List Forest)) : ChildrenReceipt :=
  let b := bestLengthMeter
    (acceptedMeter (fun F=>(FullSourceWork.agreementMeter T S F).work) T S q) r.value
  ⟨b.value,r.localWork+b.work+r.value.length+2,r.recursiveWork,r.calls,r.value⟩

def finishSource (T S : Tree) (q : Nat) (r : ForestReceipt (List Forest))
    (debits : List Nat) : WholeSourceWork.Charged (Option (List (List Nat))) :=
  let z := finishChildren T S q r
  ⟨z.value,z.localWork+debits.sum⟩

theorem finish_children_projection (h : ChildrenRun FExec T q cs r debits ticks)
    (soundValue : ∀ t ss b fr, FExec t ss b fr →
      fr.value = GenericForest.solve actual t ss b) :
    finishChildren T S q r =
      runChildrenMeter actual (fun _=>0)
        (fun F=>(FullSourceWork.agreementMeter T S F).work) T S q cs := by
  have hr := children_projection h soundValue
  simp only [finishChildren,runChildrenMeter,hr]

theorem finish_source_projection (h : ChildrenRun FExec T q cs r debits ticks)
    (soundValue : ∀ t ss b fr, FExec t ss b fr →
      fr.value = GenericForest.solve actual t ss b)
    (soundDebit : ∀ t ss b fr, FExec t ss b fr →
      fr.debit = WorkRecursion.forestWork actual (fun _ _ _=>0) t ss b) :
    finishSource T S q r debits =
      FullSourceWork.runChildrenSource actual (fun _ _ _=>0) T S q cs := by
  have hv := finish_children_projection (S:=S) h soundValue
  have hd := children_debit h soundDebit
  simp only [finishSource,FullSourceWork.runChildrenSource,hv,hd]

end SourceChildrenV2
