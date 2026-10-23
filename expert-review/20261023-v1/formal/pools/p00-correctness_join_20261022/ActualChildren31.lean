-- All actual children: literal fields, valid source partitions/embeddings and payment.
import SingletonSpan30
import ChildFields14
import EarlyFacts12
open RMAF Universal233 CherryBranching VertexGeometry SourceBoundary OwnHigh
namespace HighChildren
theorem singleton_embeddings (S : Tree) (a : Nat) (hn : (leaves S).Nodup) (ha : a∈leaves S) :
    pairwiseEmbeddings S (singletonPartition S a)=true := by
  simp only [singletonPartition,pairwiseEmbeddings,List.all_cons,List.all_nil,Bool.and_true]
  simp only [disjointVertices,List.all_eq_true,Bool.not_eq_true']
  intro z hz
  apply Bool.eq_false_iff.mpr
  intro hother
  have hleaf:=singleton_minimal_leaf S a z hn ha hz
  have hasel:=leaf_minimal_selected S ((leaves S).filter (fun x=>x != a)) z a hleaf (List.contains_iff_mem.mp hother)
  have hne:=(List.mem_filter.mp hasel).2
  simp only [bne_self_eq_false] at hne
  cases hne
theorem all_child_partitions (S : Tree) (a b : Nat) (hn : (leaves S).Nodup)
    (ha : a∈leaves S) (hb : b∈leaves S) (hab : a≠b)
    (c : Child) (hc : c∈branches S a b) :
    partitionCheck (leaves S) c.partition=true ∧ pairwiseEmbeddings S c.partition=true := by
  rcases (literal_fields S a b c hc).2.2 with rfl | rfl | rfl
  · exact ⟨singleton_partition S a b hn ha hb hab,singleton_embeddings S a hn ha⟩
  · exact ⟨singleton_partition S b a hn hb ha hab.symm,singleton_embeddings S b hn hb⟩
  · exact ⟨pendant_partition S a b hn ha,pendant_embeddings S a b hn ha⟩
def ActualChildFacts (S : Tree) (c : Child) : Prop :=
  partitionCheck (leaves S) c.partition=true ∧
  pairwiseEmbeddings S c.partition=true ∧
  c.sourceForest=c.partition.filterMap (fun B=>restrict B S) ∧
  c.partition.length=c.paid+1 ∧ c.sourceForest.length=c.paid+1 ∧ 0<c.paid
theorem actual_child_facts (S : Tree) (a b : Nat) (hn : (leaves S).Nodup)
    (ha : a∈leaves S) (hb : b∈leaves S) (hab : a≠b) (hh : 3≤(cuts S a b).length)
    (c : Child) (hc : c∈branches S a b) : ActualChildFacts S c := by
  have hp:=all_child_partitions S a b hn ha hb hab c hc
  have hf:=literal_fields S a b c hc
  exact ⟨hp.1,hp.2,hf.1,hf.2.1,source_component_count S a b c hc hp.1,positive_paid S a b hh c hc⟩
end HighChildren
namespace HighSelector
open OrdinaryDispatch FastOrdinary
theorem high_actual_children (T S : Tree) (reverse : Bool) (c : Candidate)
    (hp : DepthOne.proper T S=true) (he : early T S=.high reverse c) :
    ∀ child∈branches (Oriented reverse T S).2 c.a c.b,
      HighChildren.ActualChildFacts (Oriented reverse T S).2 child := by
  have hs:=high_selector_facts T S reverse c hp he
  have hnS : (leaves (Oriented reverse T S).2).Nodup := by
    have h:=hs.1
    simp only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1.2
  have haglabels : (leaves (Oriented reverse T S).1).Perm (leaves (Oriented reverse T S).2) := by
    have h:=hs.1
    simp only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.2
  have haT:=cherry_a_mem _ c.parent c.a c.b hs.2.1
  have hbT:=cherry_b_mem _ c.parent c.a c.b hs.2.1
  have ha:=haglabels.mem_iff.mp haT
  have hb:=haglabels.mem_iff.mp hbT
  have hab:=cherry_distinct _ _ c.parent c.a c.b hs.1 hs.2.1
  exact HighChildren.actual_child_facts _ c.a c.b hnS ha hb hab hs.2.2.2
#print axioms high_actual_children
end HighSelector
