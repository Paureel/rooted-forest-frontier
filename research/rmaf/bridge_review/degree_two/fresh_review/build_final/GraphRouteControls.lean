import ActualEmbedding
namespace DegreeTwoGraphControls
open RMAF

def edge (a b : Vertex) : Bool :=
  b == a ++ [false] || b == a ++ [true] ||
  a == b ++ [false] || a == b ++ [true]
def degree (t : Tree) (B : List Nat) (v : Vertex) : Nat :=
  if (minimalVertices B t).contains v then
    ((minimalVertices B t).eraseDups.filter (edge v)).length
  else 0

def rootT : Tree := .node (.leaf 0) (.leaf 1)
def rootU : Tree := .node (.leaf 1) (.leaf 0)
def pathT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def pathU : Tree := .node (.leaf 2) (.node (.leaf 1) (.leaf 0))
def globalT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))

def refinement (t u : Tree) (B A C : List Nat) (v : Vertex) : Bool :=
  partitionCheck B [A,C] && restrictionAgrees t u A && restrictionAgrees t u C &&
  pairwiseEmbeddings t [A,C] && pairwiseEmbeddings u [A,C] &&
  (minimalVertices A t).all (fun x => (minimalVertices B t).contains x) &&
  (minimalVertices C t).all (fun x => (minimalVertices B t).contains x) &&
  (minimalVertices A u).all (fun x => (minimalVertices B u).contains x) &&
  (minimalVertices C u).all (fun x => (minimalVertices B u).contains x) &&
  !(minimalVertices A t).contains v && !(minimalVertices C t).contains v

theorem root_control : degree rootT [0,1] [] = 2 ∧
    refinement rootT rootU [0,1] [0] [1] [] = true := by decide

theorem path_control : degree pathT [0,2] [false] = 2 ∧
    minimalVertices [0,2] pathT = [[],[false],[false,false],[true]] ∧
    refinement pathT pathU [0,2] [0] [2] [false] = true ∧
    minimalVertices [0] pathU = [[true,true]] := by decide

theorem consumer_control : agreement globalT globalT [[0,2],[1],[3]] = true ∧
    agreement globalT globalT [[0],[2],[1],[3]] = true ∧
    ([[0],[2],[1],[3]] : List (List Nat)).length =
      ([[0,2],[1],[3]] : List (List Nat)).length + 1 := by decide

theorem degree_three_control : degree pathT [0,1,2] [false] = 3 ∧
    refinement pathT pathT [0,1,2] [0] [1,2] [false] = false ∧
    refinement pathT pathT [0,1,2] [0,1] [2] [false] = false ∧
    refinement pathT pathT [0,1,2] [0,2] [1] [false] = false := by decide

theorem root_absence_control : minimalVertices [0,1] pathT =
    [[false],[false,false],[false,true]] := by decide

theorem empty_absent_singleton_control : degree rootT [] [] = 0 ∧
    degree rootT [9] [] = 0 ∧ degree rootT [0] [false] = 0 := by decide

theorem duplicates_not_unique : ¬ (leaves (.node (.leaf 0) (.leaf 0))).Nodup ∧
    ¬ ([0,0,1] : List Nat).Nodup := by decide

#print axioms root_control
#print axioms path_control
#print axioms consumer_control
#print axioms degree_three_control
#print axioms root_absence_control
#print axioms empty_absent_singleton_control
#print axioms duplicates_not_unique
end DegreeTwoGraphControls
