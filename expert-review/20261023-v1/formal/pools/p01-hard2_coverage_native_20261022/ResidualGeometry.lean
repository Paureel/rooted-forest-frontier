import ResidualPartition
import OriginalCladeSplit
namespace FreshResidual
open RMAF RestrictionBridge ForestState OutputState FreshClade

theorem source_member {S s : Tree} {P : List (List Nat)}
 (ns : (leaves S).Nodup) (hp : partitionCheck (leaves S) P=true)
 (hs : s∈sourceForest S P) : ∃U, U∈P ∧ restrict U S=some s ∧ (leaves s).Perm U := by
 rcases List.mem_filterMap.mp hs with ⟨U,hu,hr⟩
 rcases restriction_materialized ns hp hu with ⟨s',hr',he⟩
 have eq : s'=s := Option.some.inj (hr'.symm.trans hr)
 subst s'
 exact ⟨U,hu,hr,he⟩

theorem source_of_partition {S : Tree} {P : List (List Nat)}
 (ns : (leaves S).Nodup) (hp : partitionCheck (leaves S) P=true)
 {U : List Nat} (hu : U∈P) :
 ∃s, s∈sourceForest S P ∧ restrict U S=some s ∧ (leaves s).Perm U := by
 rcases restriction_materialized ns hp hu with ⟨s,hs,he⟩
 exact ⟨s,List.mem_filterMap.mpr ⟨U,hu,hs⟩,hs,he⟩

theorem materialized_restriction {T S s : Tree} {U B : List Nat}
 (hs : restrict U S=some s) (sub : ∀x,x∈B→x∈U) :
 restrictionAgrees T s B=restrictionAgrees T S B := by
 have he := restrict_subset U B sub S
 simp only [hs,Option.bind_some] at he
 unfold restrictionAgrees
 rw [he]

theorem materialized_hulls {S s : Tree} {U B C : List Nat}
 (hs : restrict U S=some s) (hb : ∀x,x∈B→x∈U) (hc : ∀x,x∈C→x∈U) :
 disjointVertices (minimalVertices B s) (minimalVertices C s)=
 disjointVertices (minimalVertices B S) (minimalVertices C S) := by
 have he := profile_restrict U B C hb hc S
 simp only [hs,optProfile] at he
 rw [←observe_profile,←observe_profile] at he
 have hm := congrArg Profile.mm he
 simp only [observe] at hm
 rw [disjoint_eq_not_hits,disjoint_eq_not_hits,hm]

theorem hull_symm {S : Tree} {B C : List Nat} (h : HullDisjoint S B C) : HullDisjoint S C B := by
 unfold HullDisjoint at h ⊢
 have he : hits (minimalVertices C S) (minimalVertices B S)=hits (minimalVertices B S) (minimalVertices C S) := by
   apply bool_ext
   simp only [hits_true]
   exact ⟨fun ⟨v,hv,hw⟩=>⟨v,hw,hv⟩,fun ⟨v,hv,hw⟩=>⟨v,hw,hv⟩⟩
 rw [disjoint_eq_not_hits] at h ⊢
 rw [he]
 exact h

theorem materialized_embeddings {S s : Tree} {U : List Nat} {F : List (List Nat)}
 (hs : restrict U S=some s) (hp : (leaves s).Perm U) :
 pairwiseEmbeddings s (family (leaves s) F)=true ↔ pairwiseEmbeddings S (family (leaves s) F)=true := by
 rw [embeddings_pairwise,embeddings_pairwise]
 apply List.Pairwise.iff_of_mem
 intro B C hb hc
 have bs := ((family_mem (leaves s) B F).mp hb).2
 have cs := ((family_mem (leaves s) C F).mp hc).2
 unfold HullDisjoint
 rw [materialized_hulls hs (fun x hx=>hp.mem_iff.mp (bs x hx)) (fun x hx=>hp.mem_iff.mp (cs x hx))]

theorem original_to_local_embeddings {S s : Tree} {U : List Nat} {F : List (List Nat)}
 (hs : restrict U S=some s) (hp : (leaves s).Perm U) (he : pairwiseEmbeddings S F=true) :
 pairwiseEmbeddings s (family (leaves s) F)=true := by
 apply (materialized_embeddings hs hp).mpr
 apply (embeddings_pairwise _ _).mpr
 exact ((embeddings_pairwise _ _).mp he).filter _

theorem local_to_original_embeddings {S : Tree} {P F : List (List Nat)}
 (ns : (leaves S).Nodup) (hp : partitionCheck (leaves S) P=true)
 (hf : partitionCheck (leaves S) F=true) (ep : pairwiseEmbeddings S P=true)
 (ref : VertexGeometry.Refines F P)
 (localE : ∀s∈sourceForest S P,pairwiseEmbeddings s (family (leaves s) F)=true) :
 pairwiseEmbeddings S F=true := by
 apply (embeddings_pairwise _ _).mpr
 apply (partition_blocks_nodup hf).imp_of_mem
 intro B C hb hc ne
 rcases ref B hb with ⟨U,hu,bs⟩
 rcases ref C hc with ⟨V,hv,cs⟩
 by_cases he : U=V
 · subst V
   rcases source_of_partition ns hp hu with ⟨s,hsm,hs,hperm⟩
   have eb : B∈family (leaves s) F := (family_mem _ _ _).mpr ⟨hb,fun x hx=>hperm.mem_iff.mpr (bs x hx)⟩
   have ec : C∈family (leaves s) F := (family_mem _ _ _).mpr ⟨hc,fun x hx=>hperm.mem_iff.mpr (cs x hx)⟩
   have hh := (embeddings_pairwise _ _).mp ((materialized_embeddings hs hperm).mp (localE s hsm))
   exact pairwise_distinct hull_symm hh eb ec ne
 · have hh := pairwise_distinct hull_symm ((embeddings_pairwise _ _).mp ep) hu hv he
   exact disjoint_mono bs cs hh
end FreshResidual

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshResidual.source_member
#print axioms FreshResidual.source_member
#check @FreshResidual.source_of_partition
#print axioms FreshResidual.source_of_partition
#check @FreshResidual.materialized_restriction
#print axioms FreshResidual.materialized_restriction
#check @FreshResidual.materialized_hulls
#print axioms FreshResidual.materialized_hulls
#check @FreshResidual.hull_symm
#print axioms FreshResidual.hull_symm
#check @FreshResidual.materialized_embeddings
#print axioms FreshResidual.materialized_embeddings
#check @FreshResidual.original_to_local_embeddings
#print axioms FreshResidual.original_to_local_embeddings
#check @FreshResidual.local_to_original_embeddings
#print axioms FreshResidual.local_to_original_embeddings
