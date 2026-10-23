import Exhaustive
import AdmissionBridge
namespace Universal233.Hard2Overlap
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification Rule5FinalClassification PaidAssembly OrdinaryPriorityBridge

def runHard2 (T S : Tree) (c : Candidate) : Option Result :=
 match c.originalCuts with
 | [p,r] => select T (leftParent S p) (rightParent S r) (rootParent S p r)
 | _ => none

theorem pendant_eq_literal {S : Tree} {a b : Nat} {p r : RMAF.Vertex}
 (hc : cuts S a b=[p,r]) : pendantPartition S a b=[leftParent S p,rightParent S r,rootParent S p r] := by
 simp only [pendantPartition,coreLabels,hc,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
   List.flatten_cons,List.flatten_nil,List.append_nil,leftParent,rightParent,rootParent]
 congr 2
 apply congrArg (fun L : List Nat => [L])
 apply List.filter_congr
 intro x hx
 simp only [List.contains_append,Bool.not_or]

/-- Original source geometry is constructed before inspecting the unknown F. -/
theorem actual_source_inputs {T S : Tree} {c : Candidate}
 (proper : DepthOne.proper T S=true) (selected : CherryBranching.select T S=some (.hard2,c)) :
 ∃p r,c.originalCuts=[p,r] ∧ cuts S c.a c.b=[p,r] ∧
 LiteralOriginalThree S p r ∧
 partitionCheck (leaves S) [leftParent S p,rightParent S r,rootParent S p r]=true ∧
 pairwiseEmbeddings S [leftParent S p,rightParent S r,rootParent S p r]=true ∧
 pendantPartition S c.a c.b=[leftParent S p,rightParent S r,rootParent S p r] := by
 have actual := selected_actual selected
 obtain ⟨p,r,hcr⟩ := list_two_named c.originalCuts (selected_spec selected).2.1
 have hc : cuts S c.a c.b=[p,r] := actual.2.symm.trans hcr
 obtain ⟨ht,hs,perm⟩ := proper_parts proper
 have ha : c.a∈leaves S := perm.mem_iff.1 (leafAt_label T _ c.a (cherry_left actual.1))
 have hq : p∈pendantOriginal S c.a c.b := by change p∈cuts S c.a c.b; simp [hc]
 have hr : r∈pendantOriginal S c.a c.b := by change r∈cuts S c.a c.b; simp [hc]
 have ne : p≠r := by
  have nd : (cuts S c.a c.b).Nodup := pendantOriginal_nodup S c.a c.b
  simpa [hc] using nd
 have graph := literalOriginalThree_construct hs ha hq hr ne
 exact ⟨p,r,hcr,hc,graph,literalThree_partition hs hq hr ne graph,PairAssembly.hard_parent_embeddings hs graph,pendant_eq_literal hc⟩

theorem actual_hard2_exhaustive {T S : Tree} {c : Candidate}
 (proper : DepthOne.proper T S=true) (selected : CherryBranching.select T S=some (.hard2,c)) :
 ∃p r out,c.originalCuts=[p,r] ∧ cuts S c.a c.b=[p,r] ∧
 LiteralOriginalThree S p r ∧
 partitionCheck (leaves S) [leftParent S p,rightParent S r,rootParent S p r]=true ∧
 pairwiseEmbeddings S [leftParent S p,rightParent S r,rootParent S p r]=true ∧
 runHard2 T S c=some out ∧ Valid T (leftParent S p) (rightParent S r) (rootParent S p r) out := by
 obtain ⟨p,r,hcr,hc,graph,hp,he,eq⟩ := actual_source_inputs proper selected
 obtain ⟨ht,hs,perm⟩ := proper_parts proper
 obtain ⟨out,hout,hvalid⟩ := select_exhaustive ht (fun x hx=>perm.mem_iff.2 hx) hp
 exact ⟨p,r,out,hcr,hc,graph,hp,he,by simpa [runHard2,hcr] using hout,hvalid⟩

theorem actual_disjoint_admission_iff {T S : Tree} {c d : Candidate}
 (proper : DepthOne.proper T S=true)
 (forward : CherryBranching.select T S=some (.hard2,c))
 (reverse : CherryBranching.select S T=some (.hard2,d))
 (noT : Rule4.select T S=none) (noS : Rule4.select S T=none)
 (selected : runHard2 T S c=some .disjoint) :
 admitted T S c.a c.b=true ↔
 ((pendantPartition S c.a c.b).filter (fun B=>restrictionAgrees T S B)).length=2 := by
 obtain ⟨p,r,hcr,hc,graph,hp,he,eq⟩ := actual_source_inputs proper forward
 obtain ⟨ht,hs,perm⟩ := proper_parts proper
 have sel : select T (leftParent S p) (rightParent S r) (rootParent S p r)=some .disjoint := by simpa [runHard2,hcr] using selected
 have hv := select_sound ht (fun x hx=>perm.mem_iff.2 hx) hp sel
 have embeds : pairwiseEmbeddings T (pendantPartition S c.a c.b)=true := by rw [eq]; exact hv
 simpa only [embeds,true_and] using actual_rule5_admitted_iff proper forward reverse noT noS
end Universal233.Hard2Overlap
