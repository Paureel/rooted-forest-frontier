import PlannerSources
import OriginalPaid
import ResidualConsumer

namespace Universal233.BothBad
open RMAF CoreProgram

abbrev ForestSolver := Option Tree → List Tree → Nat → Option Forest

structure Call where
  target : Option Tree
  sources : List Tree
  budget : Nat

structure Execution where
  answer : Option Forest
  calls : List Call

def asTree (solve : ForestSolver) (t s : Tree) (b : Nat) : Option Forest := solve (some t) [s] b

def ordinaryExecution (solve : ForestSolver) (T S : Tree) (Q : Forest) (b : Nat) : Execution :=
  match MafScheduler.prepare T S Q with
  | none => ⟨none,[]⟩
  | some js =>
    let r := PaidQueries.meterSchedule (MafScheduler.recursive T S (asTree solve)) (fun _ _ => 0) b js
    ⟨r.value.answers.map (fun xs => xs.flatMap Prod.snd),
      r.queries.filterMap (fun ub => match restrict ub.1 T,restrict ub.1 S with
        | some t,some s => some ⟨some t,[s],ub.2⟩
        | _,_ => none)⟩

theorem ordinaryExecution_value (solve : ForestSolver) (T S : Tree) (Q : Forest) (b : Nat) :
    (ordinaryExecution solve T S Q b).answer=MafScheduler.solveDisjoint T S (asTree solve) b Q := by
  cases hp : MafScheduler.prepare T S Q with
  | none => simp [ordinaryExecution,MafScheduler.solveDisjoint,MafScheduler.attempt,hp]
  | some js => simp [ordinaryExecution,hp,PaidQueries.meterSchedule_value,
      MafScheduler.solveDisjoint,MafScheduler.attempt]

/-- Every recursive call is made on its actual stored target, whole current
    source list and guarded budget. No whole-B tree replaces a B forest. -/
def dispatch (solve : ForestSolver) (T S : Tree) (e : Entry) : Execution :=
  match e.mode with
  | .ordinary => ordinaryExecution solve T S e.output.partition e.budget
  | .full =>
    let ss := OutputState.sourceForest S e.output.partition
    ⟨solve (some T) ss e.budget,[⟨some T,ss,e.budget⟩]⟩
  | .retained _ residual completed known =>
    let tb := ForestGroups.localTarget (some T) residual
    let bs := ForestGroups.owned (OutputState.sourceForest S e.output.partition) residual
    ⟨(solve tb bs e.budget).map (fun F => known++F++[completed]),[⟨tb,bs,e.budget⟩]⟩

def accept (T S : Tree) (q : Nat) (F : Forest) : Bool := agreement T S F && decide (F.length-1≤q)

def checked (T S : Tree) (q : Nat) (o : Option Forest) : Option Forest :=
  o.bind (fun F => if accept T S q F then some F else none)

def choose (a b : Option Forest) : Option Forest := match a,b with
  | none,_ => b
  | _,none => a
  | some F,some G => if F.length≤G.length then some F else some G

def execute (solve : ForestSolver) (T S : Tree) (q : Nat) : List Entry → Execution
  | [] => ⟨none,[]⟩
  | e::es =>
    let r := dispatch solve T S e
    let tail := execute solve T S q es
    ⟨choose (checked T S q r.answer) tail.answer,r.calls++tail.calls⟩

def solvePair (solve : ForestSolver) (S T : Tree) (A B C : List Nat)
    (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) : Execution :=
  execute solve T S q (plan S T A B C (PairGeometry.descendants T edge.2) q)
end Universal233.BothBad
