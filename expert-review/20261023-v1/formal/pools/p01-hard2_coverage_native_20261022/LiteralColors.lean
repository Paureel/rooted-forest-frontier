-- Literal computations only; author selected-case proof bodies excluded.
import ActualAvoidance
open RMAF VertexGeometry Universal233.CoreProgram
namespace ContactedHard2Survival
def taggedColor (A B : List Nat) (ca cb cc : Nat → Nat) (x : Nat) : Nat :=
  if x ∈ A then 3 * ca x else if x ∈ B then 3 * cb x + 1 else 3 * cc x + 2

def jointLabel (T : Tree) (v w : RMAF.Vertex) (x : Nat) : Nat :=
  4 * colorLabel T v x + colorLabel T w x

def wholeOutputs (S : Tree) (A B : List Nat) (ca cb cc : Nat → Nat) (q : Nat) : List Output :=
  (generate S (taggedColor A B ca cb cc) q).outputs

def cliqueOutputs (S T : Tree) (A B : List Nat) (v : RMAF.Vertex) (q : Nat) : List Output :=
  (wholeOutputs S A B (fun _ => 0) (colorLabel T v) (colorLabel T v) q ++
    wholeOutputs S A B (colorLabel T v) (fun _ => 0) (colorLabel T v) q) ++
    wholeOutputs S A B (colorLabel T v) (colorLabel T v) (fun _ => 0) q

/-- All three literal whole-source clique calls, including duplicate outputs. -/
def fourChainOutputs (S T : Tree) (A B : List Nat) (v w : RMAF.Vertex) (q : Nat) : List Output :=
  ((wholeOutputs S A B (fun _ => 0) (colorLabel T v) (colorLabel T w) q ++
    wholeOutputs S A B (fun _ => 0) (jointLabel T v w) (fun _ => 0) q) ++
    wholeOutputs S A B (colorLabel T v) (fun _ => 0) (colorLabel T w) q) ++
    wholeOutputs S A B (colorLabel T v) (colorLabel T w) (fun _ => 0) q

/-- The four chain calls use one joint middle generator, never a product of
independent same-parent cut sets. The geometric gate counts actual joint regions. -/
def diagonalOutputs (S T : Tree) (A B : List Nat) (v w : RMAF.Vertex) (q : Nat) : List Output :=
  wholeOutputs S A B (fun _ => 0) (jointLabel T v w) (fun _ => 0) q ++
    wholeOutputs S A B (colorLabel T v) (fun _ => 0) (colorLabel T w) q

/-- Actual paid count-two diagonal: middle joint clearing versus both outer
parents, with every recorded source cut already charged. -/
def vertexPairOutputs (S T : Tree) (A B : List Nat) (v : RMAF.Vertex) (q : Nat) : List Output :=
  wholeOutputs S A B (colorLabel T v) (fun _ => 0) (fun _ => 0) q ++
  wholeOutputs S A B (fun _ => 0) (colorLabel T v) (fun _ => 0) q

def sideColor (D : List Nat) (x : Nat) : Nat := if x ∈ D then 0 else 1

def sideOutputs (S : Tree) (A B D : List Nat) (q : Nat) : List Output :=
  wholeOutputs S A B (fun _ => 0) (sideColor D) (fun _ => 0) q

end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
