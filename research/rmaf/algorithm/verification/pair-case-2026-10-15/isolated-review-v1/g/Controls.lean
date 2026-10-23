import Selector
namespace PairGeometry.Controls
open RMAF VertexGeometry

def pair (a b : Tree) : Tree := .node a b

def t1 : Tree := pair (pair (pair (.leaf 1) (pair (.leaf 3) (.leaf 4)))
  (pair (.leaf 2) (pair (.leaf 5) (.leaf 6)))) (.leaf 7)
def rootT : Tree := pair (pair (.leaf 1) (pair (.leaf 3) (.leaf 4)))
  (pair (.leaf 2) (pair (.leaf 5) (.leaf 6)))
def a : List Nat := [1,2]
def b : List Nat := [3,4,5,6]

theorem t1_shared_exact : (minimalVertices a t1).filter (fun v => (minimalVertices b t1).contains v)=
    [[false],[false,false],[false,true]] := by decide

theorem t1_choice : choose t1 a b=some (.edge ([false],[false,false])) := by decide

theorem t1_both_clear : edgeOK t1 a b ([false],[false,false])=true ∧
    edgeOK t1 a b ([false],[false,true])=true := by decide

theorem root_choice : choose rootT a b=some (.edge ([],[false])) := by decide

theorem root_two_regions_degree : regions a rootT []=[0,1] ∧ hullDegree rootT a []=2 := by decide

theorem root_no_up_neighbor : neighbor [] 2=none := by decide

theorem boundary_orientation : (([false,false],[false])∈edges t1)=False ∧
    edgeOK t1 a b ([false,false],[false])=false := by decide

def ternary : Tree := pair (pair (.leaf 0) (.leaf 3)) (pair (.leaf 1) (pair (.leaf 2) (.leaf 4)))

theorem three_choice : choose ternary [0,1,2] [3,4]=some (.vertex [true]) := by decide

theorem three_region_count : regions [0,1,2] ternary [true]=[0,1,2] ∧ hullDegree ternary [0,1,2] [true]=3 := by decide

theorem monochromatic_sides_not_clear : edgeOK ternary [0,1,2] [3,4] ([],[true])=false := by decide

def trap : Tree := pair (pair (.leaf 0) (.leaf 1)) (pair (.leaf 2) (pair (.leaf 3) (.leaf 4)))

theorem original_unary_path : [true]∈minimalVertices [0,4] trap ∧ [true,true]∈minimalVertices [0,4] trap ∧
    leafAddress trap 4=[true,true,true] := by decide

theorem suppressed_display_address : restrict [0,4] trap=some (pair (.leaf 0) (.leaf 4)) ∧
    leafAddress (pair (.leaf 0) (.leaf 4)) 4=[true] ∧ ([],[true,true,true])∉edges trap := by decide

theorem absent_label_refused : properInput t1 [1,99] b=false ∧ choose t1 [1,99] b=none := by decide

theorem repeated_target_refused : choose (pair (.leaf 1) (.leaf 1)) [1] [2]=none := by decide

theorem repeated_selection_refused : choose t1 [1,1,2] b=none := by decide

theorem empty_refused : choose t1 [] b=none := by decide

theorem singleton_outside : choose t1 [1] b=none := by decide

theorem disjoint_outside : choose (pair (pair (.leaf 0) (.leaf 1)) (pair (.leaf 2) (.leaf 3))) [0,1] [2,3]=none := by decide

theorem identical_rooted_shape : restrictionAgrees t1 t1 [1,2,3,4,5,6,7]=true := by decide

theorem wrong_rooted_topology : restrictionAgrees (pair (pair (.leaf 0) (.leaf 1)) (.leaf 2))
    (pair (.leaf 0) (pair (.leaf 1) (.leaf 2))) [0,1,2]=false := by decide

theorem false_forest_validity_rejected : agreement (pair (pair (.leaf 0) (.leaf 1)) (pair (.leaf 2) (.leaf 3)))
    (pair (pair (.leaf 0) (.leaf 1)) (pair (.leaf 2) (.leaf 3))) [[0,2],[1,3]]=false := by decide

theorem linear_search_counter : chooseCalls t1 a b+3≤4*(leaves t1).length := chooseCalls_linear t1 a b
end PairGeometry.Controls
