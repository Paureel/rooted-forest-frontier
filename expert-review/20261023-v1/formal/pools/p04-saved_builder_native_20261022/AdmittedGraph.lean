import AdmittedEarly
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open VertexGeometry Universal233.Hard2Overlap

theorem findCommon_self_none (A B : List RMAF.Vertex)
 (missing : findCommon A B B=Option.none) : disjointVertices A B=true := by
 induction A with
 | nil => rfl
 | cons a rest ih =>
  cases hit : B.contains a with
  | false =>
   have tail : findCommon rest B B=Option.none := by simpa only [findCommon,hit,Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false,ite_true] using missing
   have got:=ih tail
   simpa only [disjointVertices,List.all_cons,hit,Bool.not_false,Bool.true_and] using got
  | true =>
   have bad : some a=Option.none := by simpa only [findCommon,hit,Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false,ite_true] using missing
   cases bad

theorem select_disjoint_overlaps (T : Tree) (A B C : List Nat)
 (selected : Hard2Overlap.select T A B C=some .disjoint) :
 overlap T A B=none ∧ overlap T B C=none ∧ overlap T A C=none := by
 unfold Hard2Overlap.select at selected
 split at selected
 · exact ⟨by assumption,by assumption,by assumption⟩
 all_goals try {unfold chain at selected;split at selected <;> cases selected}
 all_goals try {unfold isolated at selected}
 all_goals obtain ⟨x,_,bad⟩:=Option.map_eq_some_iff.mp selected;cases bad

theorem select_disjoint_embeddings (T : Tree) (A B C : List Nat)
 (selected : Hard2Overlap.select T A B C=some .disjoint) :
 pairwiseEmbeddings T [A,B,C]=true := by
 have edges:=select_disjoint_overlaps T A B C selected
 have ab:=findCommon_self_none (minimalVertices A T) (minimalVertices B T) edges.1
 have bc:=findCommon_self_none (minimalVertices B T) (minimalVertices C T) edges.2.1
 have ac:=findCommon_self_none (minimalVertices A T) (minimalVertices C T) edges.2.2
 simp only [pairwiseEmbeddings,List.all_cons,List.all_nil,ab,bc,ac]
 rfl

theorem actual_partition_parents (S : Tree) (a b : Nat) (p r : RMAF.Vertex)
 (source : cuts S a b=[p,r]) :
 pendantPartition S a b=[PaidAssembly.leftParent S p,PaidAssembly.rightParent S r,PaidAssembly.rootParent S p r] := by
 simp only [pendantPartition,coreLabels,source,PaidAssembly.leftParent,PaidAssembly.rightParent,PaidAssembly.rootParent,
  List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,List.cons_append,
  List.contains_append,Bool.not_or,List.nil_append]

theorem actual_target_embeddings (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true)
 (early : OrdinaryDispatch.FastOrdinary.early T S=.hard2 c d)
 (graph : runHard2 T S c=some .disjoint) :
 pairwiseEmbeddings T (pendantPartition S c.a c.b)=true := by
 have front:=actual_front_checks T S c d proper early
 have cmem:=(select_hard2_membership_clear T S c (early_hard2_guards T S c d early).1).1
 have aligned:=(selected_candidate_source T S c cmem).2
 have len : c.originalCuts.length=2 :=by rw [aligned];exact front.2.2.2.2.1
 have two : ∃p r,c.originalCuts=[p,r] :=by
  cases form:c.originalCuts with
  | nil => rw [form] at len;simp only [List.length_cons,List.length_nil] at len;omega
  | cons p tail =>
   cases tail with
   | nil => rw [form] at len;simp only [List.length_cons,List.length_nil] at len;omega
   | cons r tail =>
    cases tail with
    | nil => exact ⟨p,r,rfl⟩
    | cons x xs => rw [form] at len;simp only [List.length_cons] at len;omega
 obtain ⟨p,r,form⟩:=two
 have cutform : cuts S c.a c.b=[p,r] :=by rw [←aligned];exact form
 rw [actual_partition_parents S c.a c.b p r cutform]
 apply select_disjoint_embeddings
 simpa only [runHard2,form] using graph
end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.findCommon_self_none
#print axioms AdmittedRule5Author.findCommon_self_none
#check @AdmittedRule5Author.select_disjoint_overlaps
#print axioms AdmittedRule5Author.select_disjoint_overlaps
#check @AdmittedRule5Author.select_disjoint_embeddings
#print axioms AdmittedRule5Author.select_disjoint_embeddings
#check @AdmittedRule5Author.actual_partition_parents
#print axioms AdmittedRule5Author.actual_partition_parents
#check @AdmittedRule5Author.actual_target_embeddings
#print axioms AdmittedRule5Author.actual_target_embeddings
