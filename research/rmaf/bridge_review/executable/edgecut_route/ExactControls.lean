import RMAF
open RMAF
namespace FreshEdgeCutControls
def sameSupport (a b : List Vertex) : Bool :=
  a.all (fun v => b.contains v) && b.all (fun v => a.contains v)
def encode (v : Vertex) : String :=
  String.ofList (v.map (fun b => if b then '1' else '0'))
def quartet_cross : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
example : sameSupport (minimalVertices [0, 2] quartet_cross) [[], [false], [false, false], [true], [true, false]] = true := by decide
#eval IO.println ("quartet_cross\t" ++ reprStr ((minimalVertices [0, 2] quartet_cross).map encode))
def quartet_single : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
example : sameSupport (minimalVertices [1] quartet_single) [[false, true]] = true := by decide
#eval IO.println ("quartet_single\t" ++ reprStr ((minimalVertices [1] quartet_single).map encode))
def quartet_left : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
example : sameSupport (minimalVertices [0, 1] quartet_left) [[false], [false, false], [false, true]] = true := by decide
#eval IO.println ("quartet_left\t" ++ reprStr ((minimalVertices [0, 1] quartet_left).map encode))
def quartet_empty : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
example : sameSupport (minimalVertices [] quartet_empty) [] = true := by decide
#eval IO.println ("quartet_empty\t" ++ reprStr ((minimalVertices [] quartet_empty).map encode))
def quartet_absent : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
example : sameSupport (minimalVertices [9] quartet_absent) [] = true := by decide
#eval IO.println ("quartet_absent\t" ++ reprStr ((minimalVertices [9] quartet_absent).map encode))
def duplicate_siblings : Tree := (.node (.leaf 0) (.leaf 0))
example : sameSupport (minimalVertices [0] duplicate_siblings) [[], [false], [true]] = true := by decide
#eval IO.println ("duplicate_siblings\t" ++ reprStr ((minimalVertices [0] duplicate_siblings).map encode))
def duplicate_cross : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 2)))
example : sameSupport (minimalVertices [0] duplicate_cross) [[], [false], [false, false], [true], [true, false]] = true := by decide
#eval IO.println ("duplicate_cross\t" ++ reprStr ((minimalVertices [0] duplicate_cross).map encode))
def root_leaf : Tree := (.leaf 0)
example : sameSupport (minimalVertices [0] root_leaf) [[]] = true := by decide
#eval IO.println ("root_leaf\t" ++ reprStr ((minimalVertices [0] root_leaf).map encode))
def root_absent : Tree := (.leaf 0)
example : sameSupport (minimalVertices [7] root_absent) [] = true := by decide
#eval IO.println ("root_absent\t" ++ reprStr ((minimalVertices [7] root_absent).map encode))
def suppressed_initial_path : Tree := (.node (.leaf 9) (.node (.leaf 8) (.node (.leaf 0) (.leaf 1))))
example : sameSupport (minimalVertices [0, 1] suppressed_initial_path) [[true, true], [true, true, false], [true, true, true]] = true := by decide
#eval IO.println ("suppressed_initial_path\t" ++ reprStr ((minimalVertices [0, 1] suppressed_initial_path).map encode))
def suppressed_single_path : Tree := (.node (.leaf 9) (.node (.leaf 8) (.leaf 0)))
example : sameSupport (minimalVertices [0] suppressed_single_path) [[true, true]] = true := by decide
#eval IO.println ("suppressed_single_path\t" ++ reprStr ((minimalVertices [0] suppressed_single_path).map encode))
def repeated_selection : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
example : sameSupport (minimalVertices [0, 0] repeated_selection) [[false, false]] = true := by decide
#eval IO.println ("repeated_selection\t" ++ reprStr ((minimalVertices [0, 0] repeated_selection).map encode))
end FreshEdgeCutControls
