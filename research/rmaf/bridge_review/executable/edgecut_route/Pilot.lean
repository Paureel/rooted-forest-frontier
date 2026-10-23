import RMAF
open RMAF
namespace FreshEdgeCutControls
def sameSupport (a b : List Vertex) : Bool :=
  a.all (fun v => b.contains v) && b.all (fun v => a.contains v)
def encode (v : Vertex) : String :=
  String.ofList (v.map (fun b => if b then '1' else '0'))
def root_leaf : Tree := (.leaf 0)
example : sameSupport (minimalVertices [0] root_leaf) [[]] = true := by decide
#eval IO.println ("root_leaf\t" ++ reprStr ((minimalVertices [0] root_leaf).map encode))
end FreshEdgeCutControls
