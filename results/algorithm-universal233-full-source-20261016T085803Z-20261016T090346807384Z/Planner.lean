import CoreCover
namespace Universal233.BothBad
open RMAF CoreProgram SourceCoverage PairAssembly BinaryCheap RankConsumer
abbrev Forest := List (List Nat)

inductive Mode where
  | ordinary
  | full
  | retained (parent residual completed : List Nat) (knownOne : Forest)

def Mode.extra : Mode → Nat
  | .retained _ _ _ _ => 1
  | _ => 0

structure Entry where
  output : Output
  mode : Mode
  budget : Nat

def entries (q : Nat) (mode : Mode) (xs : List Output) : List Entry :=
  xs.filterMap (fun o => if o.sourceCuts.length+mode.extra≤q then
    some ⟨o,mode,q-o.sourceCuts.length-mode.extra⟩ else none)

def knownOne (T S : Tree) (A : List Nat) : Option Forest :=
  match restrict A T, restrict A S with
  | some t, some s =>
    match DepthOne.pretest01 t s with
    | .found (some p) => some (DepthOne.forest s (some p))
    | _ => none
  | _, _ => none

def reuse (S : Tree) (color : Nat → Nat) (probe : List Output) (q : Nat) : List Output :=
  if probe.isEmpty then (generate S color q).outputs else probe

def cheapPlan (S T : Tree) (A B C D : List Nat) (q : Nat)
    (cheap opposite : List Output) : List Entry :=
  let good := restrictionAgrees S T (ay A D) && restrictionAgrees S T (an A D)
  if good then
    match knownOne T S A with
    | none => []
    | some F => entries q .ordinary cheap ++ entries q (.retained A B C F) opposite
  else entries q .ordinary cheap ++ entries q .full opposite

/-- No unknown F or optimum is an input. The two actual bounded probes are
    cached; any accepted list is reused, and all subtraction is guarded. -/
def plan (S T : Tree) (A B C D : List Nat) (q : Nat) : List Entry :=
  if q<3 then [] else
    let a := (fourProbe S (cheapColor A B D)).outputs
    let b := (fourProbe S (cheapColor B A D)).outputs
    if a.isEmpty then
      if b.isEmpty then entries q .full ((generate S (cheapColor A B D) q).outputs ++
        (generate S (cheapColor B A D) q).outputs)
      else cheapPlan S T B A C D q b (reuse S (cheapColor A B D) a q)
    else cheapPlan S T A B C D q a (reuse S (cheapColor B A D) b q)

def chargedCosts (xs : List Entry) : List Nat :=
  xs.map (fun e => e.output.sourceCuts.length+e.mode.extra)

def budgets (xs : List Entry) : List Nat := xs.map Entry.budget
end Universal233.BothBad
