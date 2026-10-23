import GroupState
namespace ForestGroups.Controls
open RMAF ForestState RestrictionBridge
def ordinary : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def ordinarySources : List Tree := [.node (.leaf 0) (.leaf 1), .node (.leaf 2) (.leaf 3)]
def ordinaryGroups : List (List Nat) := [[0,1],[2,3]]
example : agrees (some ordinary) ordinarySources ordinaryGroups = true := by decide
example : agrees (restrict [0,1] ordinary) [.node (.leaf 0) (.leaf 1)] [[0,1]] = true := by decide
example : agrees (restrict [2,3] ordinary) [.node (.leaf 2) (.leaf 3)] [[2,3]] = true := by decide
example : additionalCost ordinarySources ordinaryGroups = 0 := by decide
example : agrees (some ordinary) ordinarySources.reverse [[3,2],[1,0]] = true := by decide

def aT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def aS : Tree := .node (.leaf 0) (.node (.leaf 1) (.leaf 2))
def bT : Tree := .node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 5) (.leaf 6))
def b1 : Tree := .node (.leaf 3) (.leaf 5)
def b2 : Tree := .node (.leaf 4) (.leaf 6)
def target : Tree := .node aT (.node bT (.leaf 7))
def sources : List Tree := [aS,b1,b2,.leaf 7]
def groups : List (List Nat) := [[0,1,2],[3,4,5,6],[7]]
def aF : List (List Nat) := [[0,1],[2]]
def bF : List (List Nat) := [[3],[5],[4],[6]]
def cF : List (List Nat) := [[7]]
example : agrees (some aT) [aS] aF = true := by decide
example : additionalCost [aS] aF = 1 := by decide
example : agrees (some aT) [aS] [[0,1,2]] = false := by decide
example : agrees (some bT) [b1,b2] bF = true := by decide
example : additionalCost [b1,b2] bF = 2 := by decide
example : disjointVertices (minimalVertices (leaves b1) target) (minimalVertices (leaves b2) target) = false := by decide
example : agrees (some target) sources (aF ++ bF ++ cF) = true := by decide
example : additionalCost sources (aF ++ bF ++ cF) = 3 := by decide
example : disjointVertices (minimalVertices (leaves aS) target) (minimalVertices (leaves b1) target) = true := by decide
example : disjointVertices (minimalVertices (leaves aS) target) (minimalVertices (leaves b2) target) = true := by decide
example : disjointVertices (minimalVertices (leaves b1) target) (minimalVertices [7] target) = true := by decide
example : disjointVertices (minimalVertices (leaves b2) target) (minimalVertices [7] target) = true := by decide
example : agrees (some bT) [bT] [[3,4,5,6]] = true := by decide
example : agrees (some bT) [b1,b2] [[3,4,5,6]] = false := by decide

def cross1 : Tree := .node (.leaf 0) (.leaf 2)
def cross2 : Tree := .node (.leaf 1) (.leaf 3)
example : agrees (restrict [0,2] ordinary) [cross1] [[0,2]] = true := by decide
example : agrees (restrict [1,3] ordinary) [cross2] [[1,3]] = true := by decide
example : agrees (some ordinary) [cross1,cross2] [[0,2],[1,3]] = false := by decide
example : agrees none [] [] = true := by decide
example : agrees (some (.leaf 9)) [.leaf 9] [[9]] = true := by decide
example : partitionCheck [] ([] : List (List Nat)) = true := by decide
end ForestGroups.Controls
