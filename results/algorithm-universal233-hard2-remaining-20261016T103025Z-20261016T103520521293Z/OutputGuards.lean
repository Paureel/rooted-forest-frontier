import GroupInterface
import PlannerSources
import PlanActualMass
namespace Universal233.BothBadGrouped
open RMAF CoreProgram SourceCoverage PairAssembly BinaryCheap RankConsumer
open ForestState ForestGroups RestrictionBridge VertexGeometry BinaryExchange

structure OutputFacts (S : Tree) (A B C : List Nat) (o : Output) : Prop where
 part : partitionCheck (leaves S) o.partition=true
 source : pairwiseEmbeddings S o.partition=true
 refines : RefinesBlocks o.partition [A,B,C]
 full_cuts : o.partition.length=o.sourceCuts.length+1
 kept : (KeptParent.Keeps A o ∨ KeptParent.Keeps B o) ∧ KeptParent.Keeps C o

theorem side_facts (S : Tree) (A B C D : List Nat) (q : Nat) (o : Output)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (ho : o∈sideOutputs S A B D q) : OutputFacts S A B C o := by
 obtain ⟨hpart,hemb⟩ := Assembly.generated_source_valid S _ q o ho
 obtain ⟨hab,hac,hbc⟩ := Assembly.parent_partition_disjoint S A B C hp
 have ref := Assembly.tagged_output_refines_parents S A B C (fun _ => 0) (sideColor D)
   (fun _ => 0) q o ho hp hab hac hbc
 have keep := KeptParent.generated_keeps_A_C S A B C (sideColor D) hp he q o ho
 exact ⟨hpart,hemb,ref,RankDichotomy.generate_partition_cost S _ q o ho,Or.inl keep.1,keep.2⟩

theorem outputs_facts (S : Tree) (A B C D : List Nat) (q : Nat) (o : Output)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (ho : o∈BothBad.outputs S A B D q) : OutputFacts S A B C o := by
 rcases List.mem_append.1 ho with hB|hA
 · have f := side_facts S B A C D q o (BinaryCheap.partition_swap _ A B C hp)
     (BinaryCheap.embeddings_swap _ A B C he) hB
   exact ⟨f.part,f.source,BothBad.swap_refinement _ B A C f.refines,f.full_cuts,
     by rcases f.kept.1 with h|h;exact Or.inr h;exact Or.inl h,f.kept.2⟩
 · exact side_facts S A B C D q o hp he hA

theorem bad_swap (S T : Tree) (K : List Nat) (h : restrictionAgrees S T K=false) :
 restrictionAgrees T S K=false := by
 cases hx : restrictionAgrees T S K with
 | false => rfl
 | true => have good := restriction_agrees_swap T S K hx;simp [h] at good

/-- Every actual original output supplies the new consumer's full grouped
interface. Kept block orders are transported through actual SameMembers. -/
theorem output_jobs (S T : Tree) (A B C D : List Nat) (q : Nat) (o : Output)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (badC : restrictionAgrees S T C=false) (hac : Disj T A C) (hbc : Disj T B C)
 (ho : o∈BothBad.outputs S A B D q) :
 let ss := OutputState.sourceForest S o.partition
 ∃ js,GroupedFullQuery.prepare (GroupedFullQuery.groupProblems (some T) ss [A++B,C])=some js ∧
 PaidQueries.badSlots js≥2 ∧ proper (some T) ss=true ∧
 partitionCheck (labels (some T)) [A++B,C]=true ∧
 Owns ss [A++B,C] ∧ CrossClear (some T) ss [A++B,C] ∧ OutputFacts S A B C o := by
 have f := outputs_facts S A B C D q o hp he ho
 obtain ⟨proper,part,own,cross⟩ := GroupedFullQuery.abc_geometry T S o.partition A B C hs ht same f.part hp f.refines hac hbc
 obtain ⟨js,prep⟩ := GroupedFullQuery.prepare_groups_exists (some T) _ [A++B,C] proper part own
 have posAB : ∀ F,GroupedFullQuery.valid (GroupedFullQuery.groupProblem (some T) (OutputState.sourceForest S o.partition) (A++B)) F →
     0<GroupedFullQuery.cost (GroupedFullQuery.groupProblem (some T) (OutputState.sourceForest S o.partition) (A++B)) F := by
   rcases f.kept.1 with keepA|keepB
   · obtain ⟨K,hK,hKA⟩ := keepA
     exact GroupedFullQuery.kept_bad_group_positive T S o.partition [A++B,C] K (A++B) hs ht same f.part part hK
       (by simp) (fun x hx => List.mem_append_left B ((hKA x).1 hx))
       (bad_swap S T K ((KeptParent.restriction_agrees_same_members S T K A hKA).trans badA))
   · obtain ⟨K,hK,hKB⟩ := keepB
     exact GroupedFullQuery.kept_bad_group_positive T S o.partition [A++B,C] K (A++B) hs ht same f.part part hK
       (by simp) (fun x hx => List.mem_append_right A ((hKB x).1 hx))
       (bad_swap S T K ((KeptParent.restriction_agrees_same_members S T K B hKB).trans badB))
 obtain ⟨KC,hKC,hKCC⟩ := f.kept.2
 have posC := GroupedFullQuery.kept_bad_group_positive T S o.partition [A++B,C] KC C hs ht same f.part part hKC
   (by simp) (fun x hx => (hKCC x).1 hx)
   (bad_swap S T KC ((KeptParent.restriction_agrees_same_members S T KC C hKCC).trans badC))
 exact ⟨js,prep,GroupedFullQuery.prepare_two_bad _ _ js prep posAB posC,proper,part,own,cross,f⟩

theorem plan_output_jobs (S T : Tree) (A B C : List Nat) (edge : RMAF.Vertex × RMAF.Vertex)
 (q : Nat) (e : BothBad.Entry) (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (he : pairwiseEmbeddings S [A,B,C]=true)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false)
 (badC : restrictionAgrees S T C=false) (hac : Disj T A C) (hbc : Disj T B C)
 (selected : PairGeometry.choose T A B=some (.edge edge))
 (emitted : e∈BothBad.plan S T A B C (PairGeometry.descendants T edge.2) q) :
 let ss := OutputState.sourceForest S e.output.partition
 ∃ js,GroupedFullQuery.prepare (GroupedFullQuery.groupProblems (some T) ss [A++B,C])=some js ∧ PaidQueries.badSlots js≥2 := by
 have mem := BothBad.plan_sources S T A B C edge hs ht (fun x hx => (same x).2 hx) hp selected q e emitted
 obtain ⟨js,prep,bad,_,_,_,_,_⟩ := output_jobs S T A B C _ q e.output hs ht same hp he badA badB badC hac hbc mem
 exact ⟨js,prep,bad⟩
end Universal233.BothBadGrouped
