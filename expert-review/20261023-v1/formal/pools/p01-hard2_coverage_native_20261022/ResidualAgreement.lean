import ResidualGeometry
namespace FreshResidual
open RMAF RestrictionBridge ForestState OutputState FreshClade

theorem original_materialized_iff {T S : Tree} {P F : List (List Nat)}
 (proper : Universal233.DepthOne.proper T S=true)
 (pp : partitionCheck (leaves S) P=true) (ep : pairwiseEmbeddings S P=true) :
 ForestState.agrees (some T) (sourceForest S P) F=true ↔
 agreement T S F=true ∧ VertexGeometry.Refines F P := by
 have proper' := proper
 simp only [Universal233.DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at proper'
 have ns := proper'.1.2
 constructor
 · intro h
   simp only [ForestState.agrees,Bool.and_eq_true,List.all_eq_true] at h
   rcases h with ⟨⟨⟨⟨_pr,pt⟩,owners⟩,et⟩,sources⟩
   have ref : VertexGeometry.Refines F P := by
     intro B hb
     rcases List.any_eq_true.mp (owners B hb) with ⟨s,hs,hbs⟩
     rcases source_member ns pp hs with ⟨U,hu,hr,hperm⟩
     exact ⟨U,hu,fun x hx=>hperm.mem_iff.mp ((contained_iff _ _).mp hbs x hx)⟩
   have ps : partitionCheck (leaves S) F=true := by
     rw [←partition_labels_perm (leaves T) (leaves S) F proper'.2]
     exact pt
   have shapes : ∀B∈F,restrictionAgrees T S B=true := by
     intro B hb
     rcases ref B hb with ⟨U,hu,sub⟩
     rcases source_of_partition ns pp hu with ⟨s,hs,hr,hperm⟩
     have fam : B∈family (leaves s) F := (family_mem _ _ _).mpr ⟨hb,fun x hx=>hperm.mem_iff.mpr (sub x hx)⟩
     have sc := sources s hs
     simp only [sourceCheck,Bool.and_eq_true,List.all_eq_true,targetAgrees] at sc
     have sh := sc.1.2 B fam
     rw [materialized_restriction hr sub] at sh
     exact sh
   have localE : ∀s∈sourceForest S P,pairwiseEmbeddings s (family (leaves s) F)=true := by
     intro s hs
     have sc := sources s hs
     simp only [sourceCheck,Bool.and_eq_true] at sc
     exact sc.2
   have es := local_to_original_embeddings ns pp ps ep ref localE
   refine ⟨?_,ref⟩
   simp only [agreement,Bool.and_eq_true,List.all_eq_true]
   exact ⟨⟨⟨⟨pt,ps⟩,shapes⟩,et⟩,es⟩
 · rintro ⟨a,ref⟩
   simp only [agreement,Bool.and_eq_true,List.all_eq_true] at a
   rcases a with ⟨⟨⟨⟨pt,ps⟩,shapes⟩,et⟩,es⟩
   simp only [ForestState.agrees,Bool.and_eq_true,List.all_eq_true]
   refine ⟨⟨⟨⟨sourceForest_proper proper pp,pt⟩,?_⟩,et⟩,?_⟩
   · intro B hb
     rcases ref B hb with ⟨U,hu,sub⟩
     rcases source_of_partition ns pp hu with ⟨s,hs,hr,hperm⟩
     apply List.any_eq_true.mpr
     exact ⟨s,hs,(contained_iff _ _).mpr (fun x hx=>hperm.mem_iff.mpr (sub x hx))⟩
   · intro s hs
     rcases source_member ns pp hs with ⟨U,hu,hr,hperm⟩
     simp only [sourceCheck,Bool.and_eq_true,List.all_eq_true]
     refine ⟨⟨?_,?_⟩,original_to_local_embeddings hr hperm es⟩
     · rw [partition_labels_perm (leaves s) U _ hperm,family_perm (leaves s) U F hperm]
       exact family_partition pp ps ref hu
     · intro B hb
       have hm := (family_mem _ _ _).mp hb
       have sub : ∀x,x∈B→x∈U := fun x hx=>hperm.mem_iff.mp (hm.2 x hx)
       simp only [targetAgrees,materialized_restriction hr sub]
       exact shapes B hm.1

#print axioms original_materialized_iff
end FreshResidual

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshResidual.original_materialized_iff
#print axioms FreshResidual.original_materialized_iff
