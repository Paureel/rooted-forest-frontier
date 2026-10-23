-- Exact frozen computational slices; no author selector proof imported/applied.
import PairIsolationV2
import Selector
open RMAF VertexGeometry
namespace ContactedHard2Overlap
inductive Order where
 | abc | acb | bac | bca
 deriving DecidableEq,Repr
def first (o : Order) (A B C : List Nat) : List Nat :=
 match o with | .abc => A | .acb => A | .bac => B | .bca => B
def second (o : Order) (A B C : List Nat) : List Nat :=
 match o with | .abc => B | .acb => C | .bac => A | .bca => C
def third (o : Order) (A B C : List Nat) : List Nat :=
 match o with | .abc => C | .acb => B | .bac => C | .bca => A
def parents (o : Order) (A B C : List Nat) : List (List Nat) :=
 [first o A B C,second o A B C,third o A B C]
def overlap (T : Tree) (A B : List Nat) : Option RMAF.Vertex :=
 findCommon (minimalVertices A T) (minimalVertices B T) (minimalVertices B T)
def Clear (T : Tree) (A B : List Nat) : Prop :=
 ∀v,v∈minimalVertices A T → v∉minimalVertices B T

inductive Result where
 | disjoint
 | clique : RMAF.Vertex → Result
 | four : Order → RMAF.Vertex → RMAF.Vertex → Result
 | diagonal : Order → RMAF.Vertex → RMAF.Vertex → Result
 | pair : Order → PairGeometry.Choice → Result
 deriving DecidableEq,Repr

def chain (T : Tree) (A B C : List Nat) (o : Order) (v w : RMAF.Vertex) : Result :=
 if (jointColors (second o A B C) T v w).length=2 then .diagonal o v w else .four o v w
def isolated (T : Tree) (A B C : List Nat) (o : Order) : Option Result :=
 (PairGeometry.choose T (first o A B C) (second o A B C)).map (Result.pair o)

/-- Every test is on the original target hull lists and literal parent labels. -/
def select (T : Tree) (A B C : List Nat) : Option Result :=
 match overlap T A B,overlap T B C,overlap T A C with
 | none,none,none => some .disjoint
 | some v,some w,none => some (chain T A B C .abc v w)
 | some v,none,some w => some (chain T A B C .bac v w)
 | none,some w,some v => some (chain T A B C .acb v w)
 | some _,none,none => isolated T A B C .abc
 | none,none,some _ => isolated T A B C .acb
 | none,some _,none => isolated T A B C .bca
 | some _,some _,some _ => (findCommon (minimalVertices A T) (minimalVertices B T) (minimalVertices C T)).map Result.clique

def ChainGuards (T : Tree) (A B C : List Nat) (v w : RMAF.Vertex) : Prop :=
 ¬selectedLeaves (leaves T) T v ∧ ¬selectedLeaves (leaves T) T w ∧
 v∈minimalVertices A T ∧ v∈minimalVertices B T ∧
 w∈minimalVertices B T ∧ w∈minimalVertices C T ∧ Clear T A C ∧ v≠w

/-- Conclusion only: actual original geometric guards, with no cover/mass input. -/
def Valid (T : Tree) (A B C : List Nat) : Result → Prop
 | .disjoint => pairwiseEmbeddings T [A,B,C]=true
 | .clique v => ¬selectedLeaves (leaves T) T v ∧ v∈minimalVertices A T ∧ v∈minimalVertices B T ∧ v∈minimalVertices C T
 | .four o v w => ChainGuards T (first o A B C) (second o A B C) (third o A B C) v w ∧ 3≤(jointColors (second o A B C) T v w).length
 | .diagonal o v w => ChainGuards T (first o A B C) (second o A B C) (third o A B C) v w ∧ (jointColors (second o A B C) T v w).length=2
 | .pair o choice => Clear T (first o A B C) (third o A B C) ∧ Clear T (second o A B C) (third o A B C) ∧
     PairGeometry.choose T (first o A B C) (second o A B C)=some choice ∧
     PairGeometry.ValidChoice T (first o A B C) (second o A B C) choice
end ContactedHard2Overlap

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
