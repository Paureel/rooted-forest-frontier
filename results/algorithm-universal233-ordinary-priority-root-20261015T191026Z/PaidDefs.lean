import CallerSetup
namespace OrdinaryCommonSplit.Caller
open RMAF

abbrev Forest := List (List Nat)
structure Job where
  T : Tree
  S : Tree
  budget : Nat
  deriving DecidableEq, Repr

def paidJobs (d : Setup) (q : Nat) : List Job :=
  if q=0 then [] else [⟨d.tx,d.sx,q-1⟩,⟨d.mxT,d.mxS,q-1⟩]

def runPaid (d : Setup) (q : Nat) (FY FN : Forest)
    (cb : Tree→Tree→Nat→Option Forest) : Option Forest :=
  match (paidJobs d q).map (fun j=>cb j.T j.S j.budget) with
  | [some FX,some FM] =>
      match reconstruct d FX FY FM FN with
      | none => none
      | some G => if G.length-1≤q then some G else none
  | _ => none

/-- Standard conditional recursion hypothesis, only on actual listed jobs.
This is not an implemented recursively exact solver. -/
def BoundedExact (T S : Tree) (q : Nat) : Option Forest→Prop
  | none => ∀G,agreement T S G=true→q<G.length-1
  | some F => agreement T S F=true ∧ F.length-1≤q ∧
      ∀G,agreement T S G=true→F.length-1≤G.length-1

def ActualIH (d : Setup) (q : Nat) (cb : Tree→Tree→Nat→Option Forest) : Prop :=
  ∀j∈paidJobs d q,BoundedExact j.T j.S j.budget (cb j.T j.S j.budget)
end OrdinaryCommonSplit.Caller
