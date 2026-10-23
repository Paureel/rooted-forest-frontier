import PlannerWork
namespace Universal233.BothBad
open RMAF CoreProgram CoreWork

def forestCells (F : Forest) : Nat := F.length+F.flatten.length
def answerCells (o : Option Forest) : Nat := o.elim 0 forestCells
def outputCells (o : Output) : Nat := forestCells o.partition+o.sourceCuts.length+
  (o.sourceCuts.map List.length).sum

def callerUnit (T S : Tree) (q : Nat) : Nat :=
  1048576*(treeNodes T+treeNodes S+q+2)^12

structure WorkProfile where
  value : Execution
  callerWork : Nat
  recursiveWork : Nat

/-- Conservative source billing annotation. Returned payload size, all local
pretests/materialization and the actual left append spine remain visible.
The source-to-primitive correspondence is a separate inspection obligation. -/
def profileExecute (solve : ForestSolver) (charge : Call → Nat) (T S : Tree) (q : Nat) :
    List Entry → WorkProfile
  | [] => ⟨⟨none,[]⟩,callerUnit T S q,0⟩
  | e::es =>
    let r := dispatch solve T S e
    let tail := profileExecute solve charge T S q es
    ⟨⟨choose (checked T S q r.answer) tail.value.answer,r.calls++tail.value.calls⟩,
      callerUnit T S q*(1+outputCells e.output+answerCells r.answer+r.calls.length)+
        r.calls.length+tail.callerWork,
      (r.calls.map charge).sum+tail.recursiveWork⟩

theorem profileExecute_value (solve : ForestSolver) (charge : Call → Nat)
    (T S : Tree) (q : Nat) (xs : List Entry) :
    (profileExecute solve charge T S q xs).value=execute solve T S q xs := by
  induction xs with
  | nil => rfl
  | cons e es ih => simp only [profileExecute,execute,ih]

theorem profileExecute_recursive (solve : ForestSolver) (charge : Call → Nat)
    (T S : Tree) (q : Nat) (xs : List Entry) :
    (profileExecute solve charge T S q xs).recursiveWork=
      ((execute solve T S q xs).calls.map charge).sum := by
  induction xs with
  | nil => rfl
  | cons e es ih => simp only [profileExecute,execute,ih,List.map_append,List.sum_append]

/-- The finite parent/side color lookup is paid per actual core request and
original leaf. Descendant calculation and plan/pretest setup are also billed. -/
def colorPrefixBill (S : Tree) (A B D : List Nat) (q : Nat) : Nat :=
  (coreRequests S A B D q).length*(leaves S).length*32*(A.length+B.length+D.length+1)

def profilePair (solve : ForestSolver) (charge : Call → Nat) (S T : Tree)
    (A B C : List Nat) (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) : WorkProfile :=
  let D := PairGeometry.descendants T edge.2
  let xs := plan S T A B C D q
  let r := profileExecute solve charge T S q xs
  ⟨r.value,callerUnit T S q*(A.length+B.length+C.length+D.length+xs.length+1)+
      corePrefixBill S A B D q+colorPrefixBill S A B D q+r.callerWork,r.recursiveWork⟩

theorem profilePair_value (solve : ForestSolver) (charge : Call → Nat) (S T : Tree)
    (A B C : List Nat) (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) :
    (profilePair solve charge S T A B C edge q).value=solvePair solve S T A B C edge q :=
  profileExecute_value solve charge T S q _

theorem profilePair_recursive (solve : ForestSolver) (charge : Call → Nat) (S T : Tree)
    (A B C : List Nat) (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) :
    (profilePair solve charge S T A B C edge q).recursiveWork=
      ((solvePair solve S T A B C edge q).calls.map charge).sum :=
  profileExecute_recursive solve charge T S q _
end Universal233.BothBad
