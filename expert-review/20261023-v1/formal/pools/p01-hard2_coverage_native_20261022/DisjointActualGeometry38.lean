import DisjointLiteralShape34
import Priority
import Partition
import SourceGuards
open RMAF Universal233 CherryBranching OrdinaryDispatch RestrictionBridge
namespace FreshLiteralDisjoint
theorem subtree_leaf_mem (T U : Tree) (v : Vertex) (sub : CoreGraph.subtree T v=some U) :
 ∀x,x∈leaves U → x∈leaves T := by
 induction v generalizing T with
 | nil =>
  change some T=some U at sub
  cases sub
  exact fun _ h=>h
 | cons b v ih =>
  cases T with
  | leaf a => change none=some U at sub;cases sub
  | node L R =>
   cases b
   · change CoreGraph.subtree L v=some U at sub
     intro x hx
     exact List.mem_append_left _ (ih L sub x hx)
   · change CoreGraph.subtree R v=some U at sub
     intro x hx
     exact List.mem_append_right _ (ih R sub x hx)

theorem cherry_first_leaf {T : Tree} {v : Vertex} {a b : Nat}
 (cherry : CoreGraph.CherryAt T v a b) : a∈leaves T := by
 exact subtree_leaf_mem T (.node (.leaf a) (.leaf b)) v cherry a (by simp [leaves])

theorem original_disjoint_geometry (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true)
 (selected : FastOrdinary.early T S=.hard2 c d)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint) :
 (leaves T).Nodup ∧ (leaves S).Nodup ∧ (∀x,x∈leaves T ↔ x∈leaves S) ∧
 partitionCheck (leaves T) (pendantPartition S c.a c.b)=true ∧
 partitionCheck (leaves S) (pendantPartition S c.a c.b)=true ∧
 pairwiseEmbeddings T (pendantPartition S c.a c.b)=true ∧
 pairwiseEmbeddings S (pendantPartition S c.a c.b)=true ∧
 (pendantPartition S c.a c.b).length=3 ∧ (pendantPartition S c.a c.b).length-1=2 := by
 obtain ⟨nt,ns,perm⟩:=(DepthOne.proper_iff T S).1 proper
 have same : ∀x,x∈leaves T ↔ x∈leaves S := fun _=>perm.mem_iff
 obtain ⟨ht,hs,hf,hr⟩:=original_early_hard2_fields selected
 obtain ⟨cherry,factory⟩:=selected_actual ht
 obtain ⟨p,r,horig,hdisjoint⟩:=run_disjoint_two picked
 have hcuts : cuts S c.a c.b=[p,r] := factory.symm.trans horig
 have literal:=literal_parent_shape S c.a c.b p r hcuts
 have sourcePart:=pendant_partition_check (b:=c.b) ns ((same c.a).1 (cherry_first_leaf cherry))
 have targetPart:=(partition_labels_congr (leaves T) (leaves S) (pendantPartition S c.a c.b) same).2 sourcePart
 obtain ⟨hab,hbc,hac⟩:=disjoint_empty_overlaps T _ _ _ hdisjoint
 have targetEmb:=Hard2Overlap.three_clear (Hard2Overlap.overlap_none hab) (Hard2Overlap.overlap_none hac) (Hard2Overlap.overlap_none hbc)
 rw [←literal] at targetEmb
 exact ⟨nt,ns,same,targetPart,sourcePart,targetEmb,source_embeddings ns,literal_parent_count S c.a c.b p r hcuts⟩
end FreshLiteralDisjoint

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshLiteralDisjoint.subtree_leaf_mem
#print axioms FreshLiteralDisjoint.subtree_leaf_mem
#check @FreshLiteralDisjoint.cherry_first_leaf
#print axioms FreshLiteralDisjoint.cherry_first_leaf
#check @FreshLiteralDisjoint.original_disjoint_geometry
#print axioms FreshLiteralDisjoint.original_disjoint_geometry
