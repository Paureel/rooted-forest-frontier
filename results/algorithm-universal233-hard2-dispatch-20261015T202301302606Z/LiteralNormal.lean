import ChosenOwner
namespace OrdinaryCommonSplit.Caller
open RMAF RestrictionBridge

/-- Normalizing an ACTUAL stable marked minimum supplies the original family
and the unmarked local agreement on the same chosen K/FX. The marker block is
selected from the literal output; no normalized-family hypothesis is assumed. -/
theorem literal_stable_marked_normal_form (T S t s mt ms : Tree) (X : List Nat) (y rho m : Nat)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup) (nx : X.Nodup)
    (subT : X⊆leaves T) (subS : X⊆leaves S)
    (hyT : y∈leaves T) (hyS : y∈leaves S) (hn : y∉X)
    (ht : restrict X T=some t) (hs : restrict X S=some s)
    (hmt : marked T X y rho=some mt) (hms : marked S X y rho=some ms)
    (hm : IsMinimum t s m) (F : List (List Nat))
    (ha : agreement mt ms F=true) (hc : F.length-1=m) :
    ∃ H K FX, H∈relabelForest (swap y rho) F ∧ K≠[] ∧ K⊆X ∧ (∀E∈FX,E⊆X) ∧ agreement t s (K::FX)=true ∧
      pairwiseEmbeddings T ((K++[y])::FX)=true ∧ pairwiseEmbeddings S ((K++[y])::FX)=true ∧
      restrictionAgrees T S (K++[y])=true ∧ F.length=(K::FX).length ∧
      K=H.filter (X.contains ·) ∧ FX=(relabelForest (swap y rho) F).erase H := by
  let G := relabelForest (swap y rho) F
  have lift := marked_family_lift T S mt ms X y rho nt ns nx subT subS hyT hyS hn hmt hms F ha
  have noSingle := stable_back_marker_not_singleton T S t s mt ms X y rho m
    ht hs hmt hms hn hm F ha hc
  obtain ⟨H,hH,hyH⟩ := checked_covers (y::X) G lift.1 (by simp : y∈y::X)
  obtain ⟨K,FX,outer,inner,neK,subK,subFX,len,kEq,fEq⟩ := chosen_marker_block X y G lift.1 hn noSingle H hH hyH
  have phead := BinaryExchange.partition_perm (y::X) G (H::FX) outer lift.1
  have pnorm : partitionCheck (y::X) ((K++[y])::FX)=true := by
    rw [←partition_cons_perm (y::X) H (K++[y]) FX inner]
    exact phead
  have et : pairwiseEmbeddings T ((K++[y])::FX)=true := by
    rw [←embeddings_cons_perm T H (K++[y]) FX inner]
    exact embeddings_outer_perm T G (H::FX) outer lift.2.1
  have es : pairwiseEmbeddings S ((K++[y])::FX)=true := by
    rw [←embeddings_cons_perm S H (K++[y]) FX inner]
    exact embeddings_outer_perm S G (H::FX) outer lift.2.2.1
  have topo : ∀E∈((K++[y])::FX),restrictionAgrees T S E=true := by
    intro E hE
    rcases List.mem_cons.1 hE with rfl | hE
    · have hh := lift.2.2.2 H (outer.mem_iff.2 (by simp))
      simpa only [restrictionAgrees,
        Universal233.DepthOne.restrict_members T H (K++[y]) (fun _ => inner.mem_iff),
        Universal233.DepthOne.restrict_members S H (K++[y]) (fun _ => inner.mem_iff)] using hh
    · exact lift.2.2.2 E (outer.mem_iff.2 (List.mem_cons_of_mem H hE))
  obtain ⟨vT,hvT⟩ := restriction_exists T (y::X) ⟨y,hyT,by simp⟩
  obtain ⟨vS,hvS⟩ := restriction_exists S (y::X) ⟨y,hyS,by simp⟩
  have nU := List.nodup_cons.2 ⟨hn,nx⟩
  have sUT : y::X⊆leaves T := by
    intro z hz;rcases List.mem_cons.1 hz with rfl | hz
    · exact hyT
    · exact subT hz
  have sUS : y::X⊆leaves S := by
    intro z hz;rcases List.mem_cons.1 hz with rfl | hz
    · exact hyS
    · exact subS hz
  have agr := family_restrict_agrees T S vT vS (y::X) ((K++[y])::FX) hvT hvS
    (restricted_perm T vT _ hvT nt nU sUT) (restricted_perm S vS _ hvS ns nU sUS) pnorm et es topo
  have rxT : restrict X vT=some t :=
    (restrict_inside T vT (y::X) X hvT (by intro z hz;exact List.mem_cons_of_mem y hz)).trans ht
  have rxS : restrict X vS=some s :=
    (restrict_inside S vS (y::X) X hvS (by intro z hz;exact List.mem_cons_of_mem y hz)).trans hs
  have clipped := (agreement_clip vT vS t s X ((K++[y])::FX) rxT rxS agr).1
  have neFX : ∀E∈FX,E≠[] := by
    intro E hE;exact checked_nonempty (y::X) ((K++[y])::FX) pnorm E (List.mem_cons_of_mem _ hE)
  rw [clip_normal_marker X K FX y subK neK subFX neFX hn] at clipped
  exact ⟨H,K,FX,hH,neK,subK,subFX,clipped,et,es,topo _ (by simp),
    (relabelForest_length _ F).symm.trans len,kEq,fEq⟩
end OrdinaryCommonSplit.Caller
