import QueryWork
import Witness01
import Reconstruction

namespace Universal233.MafScheduler
open RMAF PaidQueries
abbrev Forest := List (List Nat)

def properBlock (T S : Tree) (U : List Nat) : Bool :=
  decide U.Nodup && !U.isEmpty && U.all (fun x => (leaves T).contains x && (leaves S).contains x)

def slot (T S : Tree) (U : List Nat) : Option (Job (List Nat) Forest) :=
  if !properBlock T S U then none else match restrict U T, restrict U S with
  | some t, some s =>
    match DepthOne.pretest01 t s with
    | .refused => none
    | .rejected => some (.hard U)
    | .found c => some (.resolved U (DepthOne.cutCost c) (DepthOne.forest s c))
  | _, _ => none

def prepare (T S : Tree) : Forest → Option (List (Job (List Nat) Forest))
  | [] => some []
  | U::Q => (slot T S U).bind (fun j => (prepare T S Q).map (j::·))

def recursive (T S : Tree) (solve : Tree → Tree → Nat → Option Forest)
    (U : List Nat) (b : Nat) : Option (Nat × Forest) :=
  match restrict U T, restrict U S with
  | some t, some s => (solve t s b).map (fun F => (F.length-1,F))
  | _, _ => none

def attempt (T S : Tree) (solve : Tree → Tree → Nat → Option Forest)
    (q : Nat) (Q : Forest) : Option (Receipt Forest) :=
  (prepare T S Q).map (schedule (recursive T S solve) q)

def solveDisjoint (T S : Tree) (solve : Tree → Tree → Nat → Option Forest)
    (q : Nat) (Q : Forest) : Option Forest :=
  (attempt T S solve q Q).bind (fun r => r.answers.map (fun xs => xs.flatMap Prod.snd))

def calls (T S : Tree) (solve : Tree → Tree → Nat → Option Forest)
    (q : Nat) (Q : Forest) : List Nat :=
  ((attempt T S solve q Q).map Receipt.calls).getD []
end Universal233.MafScheduler
