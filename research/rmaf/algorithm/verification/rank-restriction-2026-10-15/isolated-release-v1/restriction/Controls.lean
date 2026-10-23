import RMAF

namespace RestrictionBridge.Controls
open RMAF
def T : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def Q : List (List Nat) := [[0,1],[2,3]]
def F : List (List Nat) := [[0],[1],[2,3]]
def Qbad : List (List Nat) := [[0,2],[1,3]]
def subfamily (U : List Nat) (G : List (List Nat)) :=
  G.filter (fun B => B.all (fun x => U.contains x))
def refines (G H : List (List Nat)) : Bool :=
  G.all (fun B => H.any (fun U => B.all (fun x => U.contains x)))

theorem nested : (restrict [0,1] T).bind (restrict [1]) = restrict [1] T := by decide
theorem lower_lca : restrict [0,1] T = some (.node (.leaf 0) (.leaf 1)) ∧
    minimalVertices [0,1] T = [[false],[false,false],[false,true]] ∧
    restrict [1] T = some (.leaf 1) ∧
    minimalVertices [1] (.node (.leaf 0) (.leaf 1)) = [[true]] := by decide
theorem original_agreement : agreement T T F = true := by decide
theorem disjoint_local : subfamily [0,1] F = [[0],[1]] ∧
    subfamily [2,3] F = [[2,3]] ∧
    agreement (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) [[0],[1]] = true ∧
    agreement (.node (.leaf 2) (.leaf 3)) (.node (.leaf 2) (.leaf 3)) [[2,3]] = true := by decide
theorem false_reverse : partitionCheck (leaves T) Qbad = true ∧
    agreement (.node (.leaf 0) (.leaf 2)) (.node (.leaf 0) (.leaf 2)) [[0,2]] = true ∧
    agreement (.node (.leaf 1) (.leaf 3)) (.node (.leaf 1) (.leaf 3)) [[1,3]] = true ∧
    pairwiseEmbeddings T Qbad = false ∧ agreement T T Qbad = false := by decide
theorem refinement_direction : refines F Q = true ∧ refines Q F = false := by decide
theorem exact_cost : ((Q.map (fun U => (subfamily U F).length - 1)).sum = F.length - Q.length) ∧
    (Q.map (fun U => (subfamily U F).length - 1)).sum ≠ F.length - 1 := by decide
end RestrictionBridge.Controls
