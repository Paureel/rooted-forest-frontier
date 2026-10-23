import CallerFinal
namespace OrdinaryCommonSplit.Source
open RMAF Universal233
def paint (T : Tree) (X : List Nat) (v : RMAF.Vertex) : Bool :=
  (minimalVertices X T).contains v
def incident (T : Tree) (X : List Nat) : List RMAF.Vertex :=
  (DepthOne.vertices T).filter fun q=> !q.isEmpty &&
    ((minimalVertices X T).contains q != (minimalVertices X T).contains q.dropLast)
end OrdinaryCommonSplit.Source
