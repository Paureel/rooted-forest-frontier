import MarkerBlock
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

theorem filter_subset_self (X B : List Nat) (sub : B⊆X) : B.filter (X.contains ·)=B :=
  List.filter_eq_self.2 (by intro x hx;exact List.contains_iff_mem.2 (sub hx))

theorem clip_subset_family (X : List Nat) (F : List (List Nat))
    (sub : ∀B∈F,B⊆X) (ne : ∀B∈F,B≠[]) : clip X F=F := by
  induction F with
  | nil => rfl
  | cons B F ih =>
    have hf := filter_subset_self X B (sub B (by simp))
    rw [clip_cons_nonempty X B F (by rw [hf];exact ne B (by simp)),hf,
      ih (by intro D hD;exact sub D (List.mem_cons_of_mem B hD))
        (by intro D hD;exact ne D (List.mem_cons_of_mem B hD))]

theorem clip_normal_marker (X K : List Nat) (F : List (List Nat)) (y : Nat)
    (subK : K⊆X) (neK : K≠[]) (subF : ∀B∈F,B⊆X) (neF : ∀B∈F,B≠[]) (hn : y∉X) :
    clip X ((K++[y])::F)=K::F := by
  have hf : (K++[y]).filter (X.contains ·)=K := by
    simp only [List.filter_append,filter_subset_self X K subK]
    simp [hn]
  rw [clip_cons_nonempty X _ F (by rw [hf];exact neK),hf,clip_subset_family X F subF neF]

/-- Normalizing an ACTUAL stable marked minimum supplies the original family
and the unmarked local agreement on the same chosen K/FX. The marker block is
selected from the literal output; no normalized-family hypothesis is assumed. -/
theorem stable_marked_normal_form (T S t s mt ms : Tree) (X : List Nat) (y rho m : Nat)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup) (nx : X.Nodup)
    (subT : X⊆leaves T) (subS : X⊆leaves S)
    (hyT : y∈leaves T) (hyS : y∈leaves S) (hn : y∉X)
    (ht : restrict X T=some t) (hs : restrict X S=some s)
    (hmt : marked T X y rho=some mt) (hms : marked S X y rho=some ms)
    (hm : IsMinimum t s m) (F : List (List Nat))
    (ha : agreement mt ms F=true) (hc : F.length-1=m) :
    ∃ K FX, K≠[] ∧ K⊆X ∧ (∀E∈FX,E⊆X) ∧ agreement t s (K::FX)=true ∧
      pairwiseEmbeddings T ((K++[y])::FX)=true ∧ pairwiseEmbeddings S ((K++[y])::FX)=true ∧
      restrictionAgrees T S (K++[y])=true ∧ F.length=(K::FX).length := by
  let G := relabelForest (swap y rho) F
  have lift := marked_family_lift T S mt ms X y rho nt ns nx subT subS hyT hyS hn hmt hms F ha
  have noSingle := stable_back_marker_not_singleton T S t s mt ms X y rho m
    ht hs hmt hms hn hm F ha hc
  obtain ⟨H,K,FX,outer,inner,neK,subK,subFX,len⟩ := checked_marker_block X y G lift.1 hn noSingle
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
  exact ⟨K,FX,neK,subK,subFX,clipped,et,es,topo _ (by simp),
    (relabelForest_length _ F).symm.trans len⟩
end OrdinaryCommonSplit
