import RMAF
open RMAF
namespace FreshEdgeCutControls
def sameSupport (a b : List Vertex) : Bool :=
  a.all (fun v => b.contains v) && b.all (fun v => a.contains v)
def encode (v : Vertex) : String :=
  String.ofList (v.map (fun b => if b then '1' else '0'))
def duplicate_siblings : Tree := (.node (.leaf 0) (.leaf 0))
example : sameSupport (minimalVertices [0] duplicate_siblings) [[false]] = true := by decide
end FreshEdgeCutControls
