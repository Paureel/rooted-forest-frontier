import RMAF
namespace RestrictionRouteControls
open RMAF
def tRoot : Tree := .node (.leaf 0) (.leaf 1)
def uRoot : Tree := .node (.leaf 1) (.leaf 0)
def tPath : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def uPath : Tree := .node (.leaf 2) (.node (.leaf 1) (.leaf 0))
def tOutside : Tree := .node (.node (.leaf 0) (.leaf 7)) (.leaf 2)
def uOutside : Tree := .node (.leaf 2) (.node (.leaf 8) (.leaf 0))
def tFour : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def adjacent (a b : Vertex) : Bool :=
  (!b.isEmpty && a == b.dropLast) || (!a.isEmpty && b == a.dropLast)
def degree (s : List Vertex) (v : Vertex) : Nat := (s.filter (adjacent v)).length
example : restrictionAgrees tRoot uRoot [0,1] = true := by decide
example : disjointVertices (minimalVertices [0] tRoot) (minimalVertices [1] tRoot) = true := by decide
example : disjointVertices (minimalVertices [0] uRoot) (minimalVertices [1] uRoot) = true := by decide
example : minimalVertices [0] tRoot = [[false]] := by decide
example : minimalVertices [0] uRoot = [[true]] := by decide
example : degree (minimalVertices [0,1] tRoot) [] = 2 := by decide
example : minimalVertices [0,2] tPath = [[],[false],[false,false],[true]] := by decide
example : minimalVertices [0] tPath = [[false,false]] := by decide
example : minimalVertices [0] uPath = [[true,true]] := by decide
example : degree (minimalVertices [0,2] tPath) [false] = 2 := by decide
example : restrictionAgrees tOutside uOutside [0,2] = true := by decide
example : restrictionAgrees tOutside uOutside [0] = true := by decide
example : restrictionAgrees tOutside uOutside [2] = true := by decide
example : leaves tOutside ≠ leaves uOutside := by decide
example : disjointVertices (minimalVertices [0] tOutside) (minimalVertices [2] tOutside) = true := by decide
example : disjointVertices (minimalVertices [0] uOutside) (minimalVertices [2] uOutside) = true := by decide
example : restrictionAgrees tFour tFour [0,2] = true := by decide
example : restrictionAgrees tFour tFour [1,3] = true := by decide
example : disjointVertices (minimalVertices [0,2] tFour) (minimalVertices [1,3] tFour) = false := by decide
example : disjointVertices (minimalVertices [0,1] tFour) (minimalVertices [2,3] tFour) = true := by decide
example : agreement tFour tFour [[0,2],[1],[3]] = true := by decide
example : agreement tFour tFour [[0],[2],[1],[3]] = true := by decide
example : ([[0],[2],[1],[3]] : List (List Nat)).length = ([[0,2],[1],[3]] : List (List Nat)).length + 1 := by decide
example : minimalVertices [] tPath = [] := by decide
example : minimalVertices [42] tPath = [] := by decide
example : (minimalVertices [0] tPath).length = 1 := by decide
example : ¬ (leaves (.node (.leaf 0) (.leaf 0))).Nodup := by decide
end RestrictionRouteControls
