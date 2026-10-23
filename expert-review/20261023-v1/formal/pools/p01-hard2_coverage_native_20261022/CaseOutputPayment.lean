import PaidOutputBinding
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram
open ContactedHard2Parent ContactedHard2Overlap
namespace ContactedHard2Survival

theorem literal_case_payment (T S : Tree) (A B C : List Nat) (q : Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (out : Result) (o : Output) (member : o∈caseOutputs S T A B C q out) (real : CutRealization.RealizedOutput S o) :
 partitionCheck (leaves S) o.partition=true ∧ pairwiseEmbeddings S o.partition=true ∧
 o.partition.length=o.sourceCuts.length+1 ∧ 2≤o.sourceCuts.length := by
 have orient : ∀ord : Order,partitionCheck (leaves S) [first ord A B C,second ord A B C,third ord A B C]=true := by
  intro ord
  exact partition_perm_own _ _ _ (IndependentReconstruction.proper_parts proper).2.1 (original_parents_perm ord A B C) part
 cases out with
 | disjoint=>simp only [caseOutputs,List.not_mem_nil] at member
 | clique v=>
  simp only [caseOutputs,cliqueOutputs,List.mem_append] at member
  rcases member with (h|h)|h
  · exact whole_source_payment T S A B C q _ _ _ proper part o h real
  · exact whole_source_payment T S A B C q _ _ _ proper part o h real
  · exact whole_source_payment T S A B C q _ _ _ proper part o h real
 | four ord v w=>
  simp only [caseOutputs,fourChainOutputs,List.mem_append] at member
  rcases member with ((h|h)|h)|h
  · exact whole_source_payment T S _ _ _ q _ _ _ proper (orient ord) o h real
  · exact whole_source_payment T S _ _ _ q _ _ _ proper (orient ord) o h real
  · exact whole_source_payment T S _ _ _ q _ _ _ proper (orient ord) o h real
  · exact whole_source_payment T S _ _ _ q _ _ _ proper (orient ord) o h real
 | diagonal ord v w=>
  simp only [caseOutputs,diagonalOutputs,List.mem_append] at member
  rcases member with h|h
  · exact whole_source_payment T S _ _ _ q _ _ _ proper (orient ord) o h real
  · exact whole_source_payment T S _ _ _ q _ _ _ proper (orient ord) o h real
 | pair ord choice=>
  cases choice with
  | vertex v=>
   simp only [caseOutputs,vertexPairOutputs,List.mem_append] at member
   rcases member with h|h
   · exact whole_source_payment T S _ _ _ q _ _ _ proper (orient ord) o h real
   · exact whole_source_payment T S _ _ _ q _ _ _ proper (orient ord) o h real
  | edge e=>
   by_cases good : restrictionAgrees S T (first ord A B C)=true
   · change o∈(if restrictionAgrees S T (first ord A B C) then sideOutputs S (first ord A B C) (second ord A B C) (PairGeometry.descendants T e.2) q
       else sideOutputs S (second ord A B C) (first ord A B C) (PairGeometry.descendants T e.2) q) at member
     rw [ite_eq_left good] at member
     exact whole_source_payment T S _ _ _ q _ _ _ proper (orient ord) o member real
   · change o∈(if restrictionAgrees S T (first ord A B C) then sideOutputs S (first ord A B C) (second ord A B C) (PairGeometry.descendants T e.2) q
       else sideOutputs S (second ord A B C) (first ord A B C) (PairGeometry.descendants T e.2) q) at member
     rw [ite_eq_right good] at member
     have swapped : partitionCheck (leaves S) [second ord A B C,first ord A B C,third ord A B C]=true :=
      partition_perm_own _ _ _ (IndependentReconstruction.proper_parts proper).2.1 (List.Perm.swap _ _ _) (orient ord)
     exact whole_source_payment T S _ _ _ q _ _ _ proper swapped o member real
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.literal_case_payment
#print axioms ContactedHard2Survival.literal_case_payment
