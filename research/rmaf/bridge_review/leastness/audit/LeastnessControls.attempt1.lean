import ActualEmbedding
namespace LeastEmbedding.Controls
open RMAF BridgeReview ExecutableBridge

theorem crossing_terminals : terminals [0,2] (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)) = [[false,false],[true,false]] := by decide
theorem crossing_support : minimalVertices [0,2] (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)) = [[],[false],[false,false],[true],[true,false]] := by decide
theorem singleton_terminals : terminals [1] (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)) = [[false,true]] := by decide
theorem singleton_support : minimalVertices [1] (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)) = [[false,true]] := by decide
theorem siblings_terminals : terminals [0,1] (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)) = [[false,false],[false,true]] := by decide
theorem siblings_support : minimalVertices [0,1] (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)) = [[false],[false,false],[false,true]] := by decide
theorem empty_terminals : terminals [] (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)) = [] := by decide
theorem empty_support : minimalVertices [] (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)) = [] := by decide
theorem absent_terminals : terminals [9] (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)) = [] := by decide
theorem absent_support : minimalVertices [9] (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)) = [] := by decide
theorem root_leaf_terminals : terminals [7] .leaf 7 = [[]] := by decide
theorem root_leaf_support : minimalVertices [7] .leaf 7 = [[]] := by decide
theorem duplicate_labels_terminals : terminals [7] (.node (.node .leaf 7 .leaf 1) (.node .leaf 2 .leaf 7)) = [[false,false],[true,true]] := by decide
theorem duplicate_labels_support : minimalVertices [7] (.node (.node .leaf 7 .leaf 1) (.node .leaf 2 .leaf 7)) = [[],[false],[false,false],[true],[true,true]] := by decide
theorem duplicate_selection_terminals : terminals [0,0,1,1] (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)) = [[false,false],[false,true]] := by decide
theorem duplicate_selection_support : minimalVertices [0,0,1,1] (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)) = [[false],[false,false],[false,true]] := by decide
theorem deep_suppression_terminals : terminals [0,1] (.node .leaf 8 (.node .leaf 8 (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)))) = [[true,true,false,false],[true,true,false,true]] := by decide
theorem deep_suppression_support : minimalVertices [0,1] (.node .leaf 8 (.node .leaf 8 (.node (.node .leaf 0 .leaf 1) (.node .leaf 2 .leaf 3)))) = [[true,true,false],[true,true,false,false],[true,true,false,true]] := by decide

def quartet : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def addedRoot : List Vertex := [[],[false],[false,false],[false,true]]
def deletedPath : List Vertex := [[],[false,false],[true],[true,false]]
def missingTerminal : List Vertex := [[false],[false,false]]
def invalidAmbient : List Vertex := [[],[false],[false,false],[true],[true,false],[false,false,false]]

def LeastSupport (ambient terminal support : List Vertex) : Prop :=
  ∀ other : ConnectedSupport,
    (∀ v, v ∈ other.first :: other.rest → v ∈ ambient) →
    (∀ v, v ∈ terminal → v ∈ other.first :: other.rest) →
    ∀ v, v ∈ support → v ∈ other.first :: other.rest

theorem sibling_true_twin_least :
    LeastSupport (vertices quartet) (terminals [0,1] quartet) (minimalVertices [0,1] quartet) := by
  intro other _ hterm v hv
  exact minimal_least [0,1] quartet other hterm v hv

theorem added_root_connected : Connected addedRoot := by
  change Connected (rootedSpan [0,1] quartet)
  exact rootedSpan_connected [0,1] quartet

theorem added_root_not_least :
    ¬ LeastSupport (vertices quartet) (terminals [0,1] quartet) addedRoot := by
  intro h
  let e := embedding [0,1] quartet 0 (by decide) (by decide)
  have hm := h e.support e.inAmbient e.containsTerminals [] (by decide)
  have hn : [] ∉ e.support.first :: e.support.rest := by
    change [] ∉ (embedding [0,1] quartet 0 _ _).support.first ::
      (embedding [0,1] quartet 0 _ _).support.rest
    rw [embedding_support_exact]
    decide
  exact hn hm

theorem deleted_path_disconnected :
    ¬ Walk (fun v => v ∈ deletedPath) [] [false,false] := by
  intro w
  have h := walk_ancestor_between w [false] (by decide) (by decide)
  exact (by decide : [false] ∉ deletedPath) h

theorem invalid_ambient_rejected :
    ¬ (∀ v, v ∈ invalidAmbient → v ∈ vertices quartet) := by
  intro h
  exact (by decide : [false,false,false] ∉ vertices quartet)
    (h [false,false,false] (by decide))

theorem missing_terminal_rejected :
    ¬ (∀ v, v ∈ terminals [0,1] quartet → v ∈ missingTerminal) := by
  intro h
  exact (by decide : [false,true] ∉ missingTerminal)
    (h [false,true] (by decide))

end LeastEmbedding.Controls
