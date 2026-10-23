import Controls
import SourceEdge
namespace BinaryExchange.T1
open RMAF VertexGeometry BinaryExchange BinaryExchange.Controls

/-- Fresh canonical set-partition enumerator, independent of X0 implementation. -/
def insertInto (x : Nat) : List (List Nat) → List (List (List Nat))
  | [] => []
  | C :: Cs => ((x :: C) :: Cs) :: (insertInto x Cs).map (C :: ·)
def partitions : List Nat → List (List (List Nat))
  | [] => [[]]
  | x :: xs => (partitions xs).flatMap (fun F => ([x] :: F) :: insertInto x F)
def refinesCheck (F P : List (List Nat)) : Bool :=
  F.all (fun C => P.any (inside C ·))

theorem refinesCheck_correct (F P : List (List Nat)) : refinesCheck F P = true ↔ Refines F P := by
  simp only [refinesCheck,List.all_eq_true,List.any_eq_true,inside_iff,Refines]

def candidates := (partitions [1,2,3,4,5,6,7]).filter (refinesCheck · P)
def retained := candidates.filter (·.contains A)
def minimum (Fs : List (List (List Nat))) : Option Nat :=
  (best List.length (agreement S T) Fs).map List.length

theorem pilot_Bell4 : (partitions [1,2,3,4]).length = 15 := by decide
set_option maxRecDepth 10000 in
theorem T1_partition_counts : (partitions [1,2,3,4,5,6,7]).length = 877 ∧
    candidates.length = 30 ∧ retained.length = 15 := by decide
set_option maxRecDepth 10000 in
theorem T1_restricted_minima : minimum candidates = some 5 ∧ minimum retained = some 5 := by decide

/-- Concrete call of the universal theorem on the pinned literal graph fixture. -/
theorem T1_universal_consumer :
    agreement S T (exchange A B F edgeSubtree) = true ∧
    Refines (exchange A B F edgeSubtree) P ∧
    (exchange A B F edgeSubtree).count A = 1 ∧
    (∀ C, C ∈ exchange A B F edgeSubtree → Sub C B →
      (∀ x, x ∈ C → x ∈ leaves edgeSubtree) ∨ (∀ x, x ∈ C → x ∉ leaves edgeSubtree)) ∧
    (exchange A B F edgeSubtree).length ≤ F.length ∧
    outside A B (exchange A B F edgeSubtree) = outside A B F := by
  apply binary_exchange S T edgeSubtree P A B [false,false]
  · decide
  · decide
  · intro x; simp [S,T,leaves,or_assoc,or_comm,or_left_comm]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · apply (executable_disjointVertices T _ _).1; decide
  · apply (executable_disjointVertices T _ _).1; decide
  · apply (executable_disjointVertices T _ _).1; decide
  · apply (executable_disjointVertices T _ _).1; decide
  · intro E hE hEA hEB
    have he : E = [7] := by
      simp only [P,List.mem_cons,List.not_mem_nil,or_false] at hE
      rcases hE with hE | hE | hE
      · exact False.elim (hEA hE)
      · exact False.elim (hEB hE)
      · exact hE
    subst E
    constructor <;> apply (executable_disjointVertices T _ _).1 <;> decide
  · decide
  · decide
  · apply (refinesCheck_correct F P).1; decide
end BinaryExchange.T1
