import LiteralSourcePartitionR3
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair ContactedSource
namespace ContactedForward

theorem pendant_source_agreement (S : Tree) (a b : Nat) (nd : (leaves S).Nodup) (aS : a∈leaves S) :
 agreement S S (Rule4.literalPartition S (cuts S a b))=true := by
 apply literal_source_agreement S _ nd (cuts_nodup_own S a b)
 · intro p hp;exact vertex_has_subtree S p (List.mem_filter.1 hp).1
 · intro p hp q hq different x xp xq
   obtain ⟨U,up⟩ := vertex_has_subtree S p (List.mem_filter.1 hp).1
   obtain ⟨V,vq⟩ := vertex_has_subtree S q (List.mem_filter.1 hq).1
   rw [subtree_labels_lookup up] at xp
   rw [subtree_labels_lookup vq] at xq
   exact pendant_clades_disjoint nd hp hq different up vq x xp xq
 · refine ⟨a,aS,?_⟩
   intro p hp ha
   obtain ⟨U,up⟩ := vertex_has_subtree S p (List.mem_filter.1 hp).1
   rw [subtree_labels_lookup up] at ha
   exact (pendant_subtree_absent_endpoints hp up).1 ha

theorem isolate_source_agreement {T S : Tree} (s : Rule4.Choice T S) :
 agreement S S (Rule4.literalPartition S [Rule4.aHead s])=true := by
 have domain := actual_forward_domain s
 have proper := IndependentReconstruction.proper_parts domain.1
 have ac := domain.2.2.1
 have head := actual_a_head s
 apply literal_source_agreement S _ proper.2.1 (List.nodup_cons.2 ⟨List.not_mem_nil,.nil⟩)
 · intro p hp
   have eq := List.mem_singleton.1 hp
   exact ⟨.leaf s.raw.a,eq ▸ head.1⟩
 · intro p hp q hq different
   exact False.elim (different ((List.mem_singleton.1 hp).trans (List.mem_singleton.1 hq).symm))
 · refine ⟨s.raw.c,(IndependentCommon.syntax_labels ac).2,?_⟩
   intro p hp
   rw [List.mem_singleton.1 hp,head.2.1]
   exact fun h=>(cherry_ne_own ac proper.2.1) (List.mem_singleton.1 h).symm

theorem emitted_source_agreement {T S : Tree} (s : Rule4.Choice T S) :
 ∀b∈Rule4.branches s,agreement b.source b.source b.partition=true := by
 intro b hb
 have proper := IndependentReconstruction.proper_parts (choice_proper s)
 have ab := ordered_sound_own T _ _ (choice_admission_own s).1
 have ac := ordered_sound_own S _ _ (choice_admission_own s).2.1
 simp only [Rule4.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
 rcases hb with rfl|rfl|rfl
 · have source := pendant_source_agreement S s.raw.a s.raw.b proper.2.1
    (proper.2.2.mem_iff.1 (IndependentCommon.syntax_labels ab).1)
   have ss : DepthOne.proper S S=true := by
    simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
     And.intro proper.2.1 (And.intro proper.2.1 (List.Perm.refl _))
   exact agreement_perm_own ss (literal_partition_perm_own S (choice_admission_own s).2.2.2.1) source
 · exact isolate_source_agreement s
 · exact pendant_source_agreement T s.raw.a s.raw.c proper.1 (proper.2.2.mem_iff.2 (IndependentCommon.syntax_labels ac).1)

theorem emitted_oriented_proper {T S : Tree} (s : Rule4.Choice T S) :
 ∀b∈Rule4.branches s,DepthOne.proper b.target b.source=true := by
 intro b hb
 simp only [Rule4.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
 rcases hb with rfl|rfl|rfl
 · exact choice_proper s
 · exact choice_proper s
 · exact proper_swap_own (choice_proper s)

theorem emitted_literal_checks {T S : Tree} (s : Rule4.Choice T S) :
 ∀b∈Rule4.branches s,
 partitionCheck (leaves b.source) b.partition=true ∧ pairwiseEmbeddings b.source b.partition=true ∧
 b.cost+1=b.partition.length ∧ b.sourceForest=OutputState.sourceForest b.source b.partition := by
 intro b hb
 have source := emitted_source_agreement s b hb
 simp only [agreement,Bool.and_eq_true] at source
 refine ⟨source.1.1.1.1,source.2,?_,rfl⟩
 change b.cuts.length+1=(Rule4.literalPartition b.source b.cuts).length
 simp only [Rule4.literalPartition,List.length_append,List.length_map,List.length_cons,List.length_nil]

end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.pendant_source_agreement
#print axioms ContactedForward.pendant_source_agreement
#check @ContactedForward.isolate_source_agreement
#print axioms ContactedForward.isolate_source_agreement
#check @ContactedForward.emitted_source_agreement
#print axioms ContactedForward.emitted_source_agreement
#check @ContactedForward.emitted_oriented_proper
#print axioms ContactedForward.emitted_oriented_proper
#check @ContactedForward.emitted_literal_checks
#print axioms ContactedForward.emitted_literal_checks
