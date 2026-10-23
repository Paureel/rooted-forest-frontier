import ScheduleAtV3

namespace SourceForestV3
open RMAF RestrictionBridge ForestState OutputState ForestGroups VertexGeometry
open Universal233 Universal233.CoreProgram Universal233.PaidQueries
open GenericForest GenericForest.FrontierWork
open SourceCouplingV2 SourceDisjointV2 SourceForestSingletonV2

abbrev F := List (List Nat)
abbrev Q := (Tree × Tree) × Nat
abbrev S := Slot (Tree × Tree) F
abbrev B := Nat × Universal233.CoreProgram.Output

structure Result where
  value : Option F
  debit : Nat
  slots : List S

def cutCount (io : B) : Nat := io.2.sourceCuts.length
def eligible (q : Nat) (io : B) : Prop := 1≤cutCount io ∧ cutCount io≤q
instance (q : Nat) (io : B) : Decidable (eligible q io) := inferInstanceAs (Decidable (_∧_))

-- This is the literal overlap branch of nonrecursiveBill, not an analytic C fee.
def overlapLocal (t : Tree) (ss : List Tree) (h : GenericForest.Overlap) (q : Nat) : Nat :=
  inspectionBill (some t) ss q +
    (overlapBill t ss + generationBill t ss h.left h.vertex q +
      generationBill t ss h.right h.vertex q +
      ((branches t ss h q).map fun io=>materializationBill t ss q io.1 io.2).sum +
      inspectionBill (some t) ss q*((branches t ss h q).length+1))

-- These are operational request/return derivations. Ordinary children occur
-- only as concrete OrdExec premises. There is no runtime base solver, W or fee.
mutual
inductive ForestExec (OrdExec : Tree → Tree → Nat → Option F → Prop) (mode : Mode) :
    Nat → Option Tree → List Tree → Nat → Result → Prop
  | improper (hp : proper T ss=false) :
      ForestExec OrdExec mode k T ss q ⟨none,inspectionBill T ss q,[]⟩
  | agreed (hp : proper T ss=true) (ha : agrees T ss (ss.map leaves)=true) :
      ForestExec OrdExec mode k T ss q ⟨some (ss.map leaves),inspectionBill T ss q,[]⟩
  | absent (hp : proper none ss=true) (ha : agrees none ss (ss.map leaves)=false) :
      ForestExec OrdExec mode k none ss q ⟨none,inspectionBill none ss q,[]⟩
  | singleton (hp : proper (some t) [s]=true) (ha : agrees (some t) [s] ([s].map leaves)=false)
      (execution : Invoke OrdExec mode k (t,s) q answer slot) :
      ForestExec OrdExec mode k (some t) [s] q
        ⟨answer.bind (checked (some t) [s] q),inspectionBill (some t) [s] q+0,[slot]⟩
  | noJobs (hp : proper (some t) ss=true) (ha : agrees (some t) ss (ss.map leaves)=false)
      (hn : ss.length≠1) (ho : overlap t ss=none) (hj : jobs t ss=none) :
      ForestExec OrdExec mode k (some t) ss q ⟨none,inspectionBill (some t) ss q,[]⟩
  | disjoint (hp : proper (some t) ss=true) (ha : agrees (some t) ss (ss.map leaves)=false)
      (hn : ss.length≠1) (ho : overlap t ss=none) (hj : jobs t ss=some js)
      (execution : ScheduleAt (PairChild OrdExec) mode q js k r slots) :
      ForestExec OrdExec mode k (some t) ss q
        ⟨r.value.answers.bind (fun xs=>checked (some t) ss q (xs.flatMap Prod.snd)),
          inspectionBill (some t) ss q+(r.callerWork+r.recursiveWork),slots⟩
  | overlap (hp : proper (some t) ss=true) (ha : agrees (some t) ss (ss.map leaves)=false)
      (hn : ss.length≠1) (ho : GenericForest.overlap t ss=some h)
      (execution : BranchesExec OrdExec mode k (some t) ss q (branches t ss h q) answers debit slots) :
      ForestExec OrdExec mode k (some t) ss q
        ⟨best List.length (GenericForest.accepted (some t) ss q) answers,
          overlapLocal t ss h q+debit,slots⟩

inductive BranchesExec (OrdExec : Tree → Tree → Nat → Option F → Prop) (mode : Mode) :
    Nat → Option Tree → List Tree → Nat → List B → List F → Nat → List S → Prop
  | nil : BranchesExec OrdExec mode k T ss q [] [] 0 []
  | skip (bad : ¬eligible q io)
      (tail : BranchesExec OrdExec mode k T ss q bs answers debit slots) :
      BranchesExec OrdExec mode k T ss q (io::bs) answers debit slots
  | take (good : eligible q io)
      (child : ForestExec OrdExec mode k T (replace ss io.1 io.2.partition) (q-cutCount io) out)
      (tail : BranchesExec OrdExec mode (k+out.slots.length) T ss q bs answers debit slots) :
      BranchesExec OrdExec mode k T ss q (io::bs)
        (match out.value with | none=>answers | some fs=>fs::answers)
        (out.debit+debit) (out.slots++slots)
end

-- Canonical comparison views appear only in the proof specification.
def branchAnswers (actual : GenericForest.FrontierWork.Ordinary)
    (T : Option Tree) (ss : List Tree) (q : Nat) (bs : List B) : List F :=
  bs.filterMap fun io=>if eligible q io then
    GenericForest.solve actual T (replace ss io.1 io.2.partition) (q-cutCount io) else none

def branchDebit (actual : GenericForest.FrontierWork.Ordinary)
    (T : Option Tree) (ss : List Tree) (q : Nat) (bs : List B) : Nat :=
  (bs.map fun io=>if eligible q io then
    OrdinaryDispatch.WorkRecursion.forestWork actual (fun _ _ _=>0)
      T (replace ss io.1 io.2.partition) (q-cutCount io) else 0).sum

def branchQueries (actual : GenericForest.FrontierWork.Ordinary)
    (T : Option Tree) (ss : List Tree) (q : Nat) (bs : List B) : List Q :=
  bs.flatMap fun io=>if eligible q io then
    frontier actual T (replace ss io.1 io.2.partition) (q-cutCount io) else []

def Corresponds (actual : GenericForest.FrontierWork.Ordinary)
    (k : Nat) (T : Option Tree) (ss : List Tree) (q : Nat) (out : Result) : Prop :=
  out.value=GenericForest.solve actual T ss q ∧
  out.debit=OrdinaryDispatch.WorkRecursion.forestWork actual (fun _ _ _=>0) T ss q ∧
  out.slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k (frontier actual T ss q)

end SourceForestV3
