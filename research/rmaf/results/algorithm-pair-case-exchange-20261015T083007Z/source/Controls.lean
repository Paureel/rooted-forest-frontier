import Exchange
namespace BinaryExchange.Controls
open RMAF BinaryExchange

def S : Tree := .node (.node (.node (.leaf 1) (.leaf 2))
  (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))) (.leaf 7)
def T : Tree := .node (.node (.node (.leaf 1) (.node (.leaf 3) (.leaf 4)))
  (.node (.leaf 2) (.node (.leaf 5) (.leaf 6)))) (.leaf 7)
def A : List Nat := [1,2]
def B : List Nat := [3,4,5,6]
def P : List (List Nat) := [A,B,[7]]
def F : List (List Nat) := [[1],[2],[3,5],[4],[6],[7]]
def edgeSubtree : Tree := .node (.leaf 1) (.node (.leaf 3) (.leaf 4))
def q (x : Nat) : Bool := (leaves edgeSubtree).contains x

theorem T1_inputs : (leaves S).Nodup ∧ (leaves T).Nodup ∧
    partitionCheck (leaves S) P = true ∧ pairwiseEmbeddings S P = true ∧
    treeAt T [false,false] = some edgeSubtree ∧ mixed A q = true ∧ mixed B q = true ∧
    restrictionAgrees S T A = true ∧ agreement S T F = true := by decide

theorem T1_mutual_clear :
    disjointVertices (minimalVertices (yes A q) T) (minimalVertices B T) = true ∧
    disjointVertices (minimalVertices (no A q) T) (minimalVertices B T) = true ∧
    disjointVertices (minimalVertices (yes B q) T) (minimalVertices A T) = true ∧
    disjointVertices (minimalVertices (no B q) T) (minimalVertices A T) = true ∧
    disjointVertices (minimalVertices [7] T) (minimalVertices A T) = true ∧
    disjointVertices (minimalVertices [7] T) (minimalVertices B T) = true := by decide

theorem T1_exact_output : exchange A B F edgeSubtree = [[1,2],[3],[5],[4],[6],[7]] := by decide

theorem T1_surgery_valid : agreement S T (exchange A B F edgeSubtree) = true ∧
    (exchange A B F edgeSubtree).length = F.length ∧
    outside A B (exchange A B F edgeSubtree) = outside A B F := by decide

def balanced : Tree := .node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))
theorem identical_clade_split : restrictionAgrees balanced balanced [1,2,3,4] = true ∧
    disjointVertices (minimalVertices [1,2] balanced) (minimalVertices [3,4] balanced) = true := by decide

def pathTree : Tree := .node (.node (.leaf 1) (.leaf 2)) (.leaf 3)
theorem suppressed_path_retained : minimalVertices [1,3] pathTree = [[],[false],[false,false],[true]] := by decide

theorem absent_empty : minimalVertices [99] T = [] := by decide
end BinaryExchange.Controls
