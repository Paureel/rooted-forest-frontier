import SourcePayment
import ActualPaid
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram
open ContactedHard2Parent ContactedHard2Overlap
namespace ContactedHard2Survival

def originalOrder : Order→Hard2Overlap.Order
 | .abc=>.abc | .acb=>.acb | .bac=>.bac | .bca=>.bca

def originalResult : Result→Hard2Overlap.Result
 | .disjoint=>.disjoint
 | .clique v=>.clique v
 | .four o v w=>.four (originalOrder o) v w
 | .diagonal o v w=>.diagonal (originalOrder o) v w
 | .pair o c=>.pair (originalOrder o) c

def caseOutputs (S T : Tree) (A B C : List Nat) (q : Nat) : Result→List Output
 | .disjoint=>[]
 | .clique v=>cliqueOutputs S T A B v q
 | .four o v w=>fourChainOutputs S T (first o A B C) (second o A B C) v w q
 | .diagonal o v w=>diagonalOutputs S T (first o A B C) (second o A B C) v w q
 | .pair o (.vertex v)=>vertexPairOutputs S T (first o A B C) (second o A B C) v q
 | .pair o (.edge e)=>Hard2PaidLocal.edgeOutputs S T (first o A B C) (second o A B C) e q

theorem literal_caseOutputs_original (S T : Tree) (A B C : List Nat) (q : Nat) (out : Result) :
 Hard2PaidLocal.caseOutputs S T A B C q (originalResult out)=caseOutputs S T A B C q out := by
 cases out with
 | disjoint=>rfl
 | clique v=>rfl
 | four o v w=>cases o <;>rfl
 | diagonal o v w=>cases o <;>rfl
 | pair o c=>cases c <;> cases o <;>rfl

theorem literal_actualOutputs_original (S T : Tree) (c : CherryBranching.Candidate) (p r : RMAF.Vertex)
 (shape : c.originalCuts=[p,r]) (q : Nat) (out : Result) :
 Hard2PaidLocal.actualOutputs S T c q (originalResult out)=
 caseOutputs S T (leftParent S p) (rightParent S r) (rootParent S p r) q out := by
 simp only [Hard2PaidLocal.actualOutputs,shape]
 exact literal_caseOutputs_original S T _ _ _ q out

theorem literal_runHardPaid_original (actual : Tree→Tree→Nat→Option (List (List Nat))) (T S : Tree) (c : CherryBranching.Candidate)
 (p r : RMAF.Vertex) (shape : c.originalCuts=[p,r]) (q : Nat) (out : Result) :
 Hard2PaidLocal.runHardPaid actual T S q c (originalResult out)=
 BothBad.execute (GenericForest.solve actual) T S q
 (BothBad.entries q .full (caseOutputs S T (leftParent S p) (rightParent S r) (rootParent S p r) q out)) := by
 simp only [Hard2PaidLocal.runHardPaid,Hard2PaidLocal.runOutputs,literal_actualOutputs_original S T c p r shape q out]
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.literal_caseOutputs_original
#print axioms ContactedHard2Survival.literal_caseOutputs_original
#check @ContactedHard2Survival.literal_actualOutputs_original
#print axioms ContactedHard2Survival.literal_actualOutputs_original
#check @ContactedHard2Survival.literal_runHardPaid_original
#print axioms ContactedHard2Survival.literal_runHardPaid_original
