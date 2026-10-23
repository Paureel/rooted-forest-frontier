import ForestTrace
namespace GenericForest.FrontierWork
open RMAF ForestState Universal233 Universal233.PaidQueries

theorem meterRun_charge_invariant {P A : Type} (solve : P → Nat → Option (Nat × A))
 (f g : P → Nat → Nat) (b : Nat) (js : List (Job P A)) :
 (meterRun solve f b js).queries=(meterRun solve g b js).queries ∧
 (meterRun solve f b js).callerWork=(meterRun solve g b js).callerWork := by
 induction js with
 | nil => exact ⟨rfl,rfl⟩
 | cons j js ih =>
  cases j with
  | resolved p c a => simp [meterRun,ih.1,ih.2]
  | hard p => cases he : solve p b <;> simp [meterRun,he,ih.1,ih.2]

theorem meterSchedule_charge_invariant {P A : Type} (solve : P → Nat → Option (Nat × A))
 (f g : P → Nat → Nat) (q : Nat) (js : List (Job P A)) :
 (meterSchedule solve f q js).queries=(meterSchedule solve g q js).queries ∧
 (meterSchedule solve f q js).callerWork=(meterSchedule solve g q js).callerWork := by
 simp only [meterSchedule]
 split
 · exact ⟨rfl,rfl⟩
 · have h:=meterRun_charge_invariant solve f g (allocated q js) js
   simp [h.1,h.2,meterRun_value]

abbrev Ordinary := Tree → Tree → Nat → Option Forest
abbrev OrdinaryWork := Tree → Tree → Nat → Nat
abbrev Query := (Tree × Tree) × Nat

def pairCallback (ordinary : Ordinary) (p : Tree × Tree) (b : Nat) : Option (Nat × Forest) :=
 (ordinary p.1 p.2 b).map (fun F=>(F.length-1,F))

def immediateQueries (ordinary : Ordinary) (T : Option Tree) (ss : List Tree) (q : Nat) : List Query :=
 if proper T ss && !agrees T ss (ss.map leaves) then
  match T,ss with
  | none,_ => []
  | some t,[s] => [((t,s),q)]
  | some t,_ => match overlap t ss with
    | some _ => []
    | none => match jobs t ss with
      | none => []
      | some js => (meterSchedule (pairCallback ordinary) (fun _ _=>0) q js).queries
 else []

/-- Source-level external callback trace of the actual forest program guards.
All raw overlapping occurrences and failed scheduler calls are retained. -/
def frontier (ordinary : Ordinary) (T : Option Tree) (ss : List Tree) (q : Nat) : List Query :=
 if proper T ss && !agrees T ss (ss.map leaves) then
  match T,ss with
  | none,_ => []
  | some t,[s] => [((t,s),q)]
  | some t,_ => match overlap t ss with
    | none => match jobs t ss with
      | none => []
      | some js => (meterSchedule (pairCallback ordinary) (fun _ _=>0) q js).queries
    | some h => (branches t ss h q).flatMap fun io=>
      let d:=io.2.sourceCuts.length
      if _hd : 1≤d ∧ d≤q then frontier ordinary T (replace ss io.1 io.2.partition) (q-d) else []
 else []
termination_by q
decreasing_by omega

def queryWork (W : OrdinaryWork) (xs : List Query) : Nat := (xs.map fun pb=>W pb.1.1 pb.1.2 pb.2).sum

def frontierPower (c : Rat) (xs : List Query) : Rat := (xs.map fun pb=>c^pb.2).sum

/-- This local premise excludes every supplied ordinary callback charge. -/
def LocalOverheadBound (ordinary : Ordinary) (T : Option Tree) (Q : Nat) (c K : Rat) : Prop :=
 LocalBillBound ordinary (fun _ _ _=>0) T Q c K
end GenericForest.FrontierWork
