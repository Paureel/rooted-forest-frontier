import Unordered
namespace Universal233.Rule5Local
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching

def earlierClear (T S : Tree) : Bool :=
 (candidates T S).all fun c => c.originalCuts.length == 2

def hasCherry (T : Tree) (a b : Nat) : Bool :=
 (cherries T).any fun (_,x,y) => (x == a && y == b) || (x == b && y == a)

/-- Exact syntactic Rule4 guard: a singleton pendant is a source cherry mate
of either endpoint. Both source orientations are tested by admitted. -/
def rule4 (T S : Tree) : Bool :=
 (candidates T S).any fun c => c.originalCuts.length == 2 &&
   c.originalCuts.any fun q => match subtreeLabels S q with
   | [x] => hasCherry S c.a x || hasCherry S c.b x
   | _ => false

def properPair (T S : Tree) : Bool :=
 decide (leaves T).Nodup && decide (leaves S).Nodup &&
 (leaves T).all (leaves S).contains && (leaves S).all (leaves T).contains

def admitted (T S : Tree) (a b : Nat) : Bool :=
 let P := pendantPartition S a b
 properPair T S && hasCherry T a b && earlierClear T S && earlierClear S T &&
 !rule4 T S && !rule4 S T && ((cuts S a b).length == 2) &&
 pairwiseEmbeddings T P && pairwiseEmbeddings S P &&
 ((P.filter fun B => restrictionAgrees T S B).length == 2)

/-- Original directed arcs with exactly one endpoint in the literal minimal
embedding. The original root has no incoming arc and is never listed. -/
def incident (T : Tree) (X : List Nat) : List RMAF.Vertex :=
 (vertices T).filter fun q => !q.isEmpty &&
   ((minimalVertices X T).contains q != (minimalVertices X T).contains q.dropLast)

def sameLabels (A B : List Nat) : Bool :=
 A.all B.contains && B.all A.contains

def refinesCheck (F P : List (List Nat)) : Bool :=
 F.all fun B => P.any fun C => B.all C.contains

theorem refinesCheck_correct (F P : List (List Nat)) :
 refinesCheck F P = true ↔ VertexGeometry.Refines F P := by
 simp [refinesCheck,VertexGeometry.Refines,List.all_eq_true,List.any_eq_true]

structure CommonSplitWitness where
 targetArc : RMAF.Vertex
 sourceArc : RMAF.Vertex
 targetDescendantX : Bool
 deriving Repr, DecidableEq

/-- A witness is retained only with its literal original target/source arcs.
The caller receives no marked-solver result. -/
def commonSplit? (T S : Tree) (a b : Nat) (X : List Nat) : Option CommonSplitWitness :=
 match incident T X with
 | [q] => match (cuts S a b).find? (fun p => sameLabels (subtreeLabels S p) X) with
   | none => none
   | some p => some ⟨q,p,sameLabels (subtreeLabels T q) X⟩
 | _ => none

end Universal233.Rule5Local
