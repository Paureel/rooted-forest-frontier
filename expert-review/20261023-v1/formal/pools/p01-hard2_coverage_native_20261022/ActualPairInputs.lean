-- Source-bound literal parent definitions only; no HardConsumer semantic proof.
import LocalDPOffsetV2
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary ContactedForward
namespace ContactedHard2Parent

def leftParent (S : Tree) (p : RMAF.Vertex) : List Nat := HardParent.subtreeLabels S p
def rightParent (S : Tree) (r : RMAF.Vertex) : List Nat := HardParent.subtreeLabels S r
def rootParent (S : Tree) (p r : RMAF.Vertex) : List Nat :=
 (leaves S).filter fun x => !(leftParent S p).contains x && !(rightParent S r).contains x

theorem actual_parent_tuple {T S : Tree} {c d : Candidate} {p r : RMAF.Vertex}
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d)
 (shape : c.originalCuts=[p,r]) :
 pendantPartition S c.a c.b=[leftParent S p,rightParent S r,rootParent S p r] := by
 have dom:=ContactedHard2.actual_hard2_domain proper selected
 have cuts : cuts S c.a c.b=[p,r] := dom.2.1.2.1.symm.trans shape
 rw [←literal_pendant_eq,cuts]
 simp only [Rule4.literalPartition,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
  List.all_cons,List.all_nil,Bool.and_true,leftParent,rightParent,rootParent]

theorem actual_permuted_source_checks {T S : Tree} {c d : Candidate} {p r : RMAF.Vertex}
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d)
 (shape : c.originalCuts=[p,r]) (X Y Z : List Nat)
 (perm : ([leftParent S p,rightParent S r,rootParent S p r] : List (List Nat)).Perm [X,Y,Z]) :
 partitionCheck (leaves S) [X,Y,Z]=true ∧ pairwiseEmbeddings S [X,Y,Z]=true := by
 have pp:=IndependentReconstruction.proper_parts proper
 have dom:=ContactedHard2.actual_hard2_domain proper selected
 have ch:=ContactedHard2.address_has_cherry dom.2.1.1
 have aS:=pp.2.2.mem_iff.1 (IndependentCommon.syntax_labels ch).1
 have source:=pendant_source_agreement S c.a c.b pp.2.1 aS
 rw [literal_pendant_eq,actual_parent_tuple proper selected shape] at source
 have properS : DepthOne.proper S S=true := by
  simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
   And.intro pp.2.1 (And.intro pp.2.1 (List.Perm.refl _))
 have permuted:=agreement_perm_own properS perm source
 simp only [agreement,Bool.and_eq_true] at permuted
 exact ⟨permuted.1.1.1.1,permuted.2⟩

theorem actual_pair_DP_allGood {T S : Tree} {c d : Candidate} {p r : RMAF.Vertex}
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d)
 (shape : c.originalCuts=[p,r]) (X Y Z : List Nat)
 (perm : ([leftParent S p,rightParent S r,rootParent S p r] : List (List Nat)).Perm [X,Y,Z])
 (goodX : restrictionAgrees S T X=true) (goodY : restrictionAgrees S T Y=true) :
 AllGoodDP.allGood (ForestGroups.localTarget (some T) (X++Y))
   (ForestGroups.owned (OutputState.sourceForest S [X,Y,Z]) (X++Y))=true := by
 have checks:=actual_permuted_source_checks proper selected shape X Y Z perm
 exact ContactedHard2DP.literal_pair_allGood T S X Y Z proper checks.1 checks.2 goodX goodY
end ContactedHard2Parent

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Parent.actual_parent_tuple
#print axioms ContactedHard2Parent.actual_parent_tuple
#check @ContactedHard2Parent.actual_permuted_source_checks
#print axioms ContactedHard2Parent.actual_permuted_source_checks
#check @ContactedHard2Parent.actual_pair_DP_allGood
#print axioms ContactedHard2Parent.actual_pair_DP_allGood
