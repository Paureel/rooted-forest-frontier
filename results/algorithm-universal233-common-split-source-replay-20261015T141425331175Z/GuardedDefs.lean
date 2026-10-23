import CallerResources
namespace OrdinaryCommonSplit.Caller
open RMAF Universal233

/-- Outer none is REFUSAL to use this source case; inner none is a proved
bounded negative answer. A total dispatcher must prove this guard succeeds or
choose another complete case. Refusal is not silently reported infeasible. -/
def runGuarded (d : Setup) (q : Nat) (cb : Tree→Tree→Nat→Option Forest) : Option (Option Forest) :=
  match DepthOne.pretest01 d.ty d.sy with
  | .found (some p) => some (runWithOutside d q (DepthOne.forest d.sy (some p)) cb)
  | _ => none

def guardedJobs (d : Setup) (q : Nat) : List Job :=
  match DepthOne.pretest01 d.ty d.sy with
  | .found (some _) => paidJobs d q
  | _ => []

def GuardedIH (d : Setup) (q : Nat) (cb : Tree→Tree→Nat→Option Forest) : Prop :=
  ∀j∈guardedJobs d q,BoundedExact j.T j.S j.budget (cb j.T j.S j.budget)
end OrdinaryCommonSplit.Caller
