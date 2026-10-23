import Pretest
namespace FreshClade
open RMAF Universal233.CoreGraph Universal233
def splitBlock (X B : List Nat) : List (List Nat) :=
 [B.filter X.contains,B.filter (fun x=>!X.contains x)].filter (fun B=>!B.isEmpty)
def splitForest (X : List Nat) (F : List (List Nat)) := F.flatMap (splitBlock X)
def balanced : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def asymm : Tree := .node (.leaf 0) (.node (.leaf 1) (.node (.leaf 2) (.leaf 3)))
def crossed : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def noHulls (T S : Tree) (F : List (List Nat)) :=
 partitionCheck (leaves T) F && partitionCheck (leaves S) F && F.all (restrictionAgrees T S)
theorem balanced_control :
 DepthOne.proper balanced balanced = true ∧
 agreement balanced balanced [[0,1,2,3]] = true ∧
 subtree balanced [false] = some (.node (.leaf 0) (.leaf 1)) ∧
 splitForest [0,1] [[0,1,2,3]] = [[0,1],[2,3]] ∧
 agreement balanced balanced (splitForest [0,1] [[0,1,2,3]]) = true := by decide
theorem nonclade_false_control :
 partitionCheck (leaves balanced) (splitForest [0,2] [[0,1,2,3]]) = true ∧
 (splitForest [0,2] [[0,1,2,3]]).all (restrictionAgrees balanced balanced) = true ∧
 pairwiseEmbeddings balanced (splitForest [0,2] [[0,1,2,3]]) = false ∧
 agreement balanced balanced (splitForest [0,2] [[0,1,2,3]]) = false ∧
 noHulls balanced balanced (splitForest [0,2] [[0,1,2,3]]) = true := by decide
theorem asymmetric_control :
 subtree asymm [true,true] = some (.node (.leaf 2) (.leaf 3)) ∧
 splitForest [2,3] [[0,1,2,3]] = [[2,3],[0,1]] ∧
 agreement asymm asymm (splitForest [2,3] [[0,1,2,3]]) = true := by decide
theorem root_control :
 subtree balanced [] = some balanced ∧
 agreement balanced balanced [[0,1],[2],[3]] = true ∧
 splitForest (leaves balanced) [[0,1],[2],[3]] = [[0,1],[2],[3]] ∧
 agreement balanced balanced (splitForest (leaves balanced) [[0,1],[2],[3]]) = true := by decide
theorem singleton_control :
 DepthOne.proper (.leaf 0) (.leaf 0) = true ∧
 agreement (.leaf 0) (.leaf 0) [[0]] = true ∧
 splitForest [0] [[0]] = [[0]] := by decide
theorem multiblock_control :
 agreement balanced balanced [[0,2],[1],[3]] = true ∧
 splitForest [0,1] [[0,2],[1],[3]] = [[0],[2],[1],[3]] ∧
 agreement balanced balanced (splitForest [0,1] [[0,2],[1],[3]]) = true := by decide
theorem repeated_control :
 DepthOne.proper (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)) = false ∧
 agreement (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)) [[0]] = true := by decide
theorem source_identity_control :
 DepthOne.proper crossed balanced = true ∧
 agreement crossed balanced [[0,1],[2],[3]] = true ∧
 subtree balanced [false] = some (.node (.leaf 0) (.leaf 1)) ∧
 subtree crossed [false] ≠ some (.node (.leaf 0) (.leaf 1)) ∧
 agreement crossed balanced (splitForest [0,1] [[0,1],[2],[3]]) = true := by decide
end FreshClade
