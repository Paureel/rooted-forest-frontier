import RMAF
open RMAF
namespace FreshEdgeCutControls
def sameSupport (a b : List Vertex) : Bool :=
  a.all (fun v => b.contains v) && b.all (fun v => a.contains v)
def encode (v : Vertex) : String :=
  String.ofList (v.map (fun b => if b then '1' else '0'))
def quartet_left : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
example : sameSupport (minimalVertices [0, 1] quartet_left) [[], [false], [false, false], [false, true]] = true := by decide
end FreshEdgeCutControls
