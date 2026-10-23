import IsoTransport

namespace AllGoodDP
open RMAF RestrictionBridge ForestState

theorem partition_labels_congr (L M : List Nat) (F : List (List Nat))
    (hlm : ∀ x, x ∈ L ↔ x ∈ M) :
    partitionCheck L F = true ↔ partitionCheck M F = true := by
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  constructor
  · rintro ⟨⟨hn,hc⟩,hs⟩
    exact ⟨⟨hn,fun x hx => hc x ((hlm x).2 hx)⟩,
      fun x hx => List.contains_iff_mem.2 ((hlm x).1 (List.contains_iff_mem.1 (hs x hx)))⟩
  · rintro ⟨⟨hn,hc⟩,hs⟩
    exact ⟨⟨hn,fun x hx => hc x ((hlm x).1 hx)⟩,
      fun x hx => List.contains_iff_mem.2 ((hlm x).2 (List.contains_iff_mem.1 (hs x hx)))⟩

theorem full_source_iso (t s : Tree)
    (hg : restrictionAgrees t s (leaves s) = true) :
    ∃ u, restrict (leaves s) t = some u ∧ RootedIso u s := by
  have hs : restrict (leaves s) s = some s :=
    restrict_of_contains s (leaves s) (by intro x hx; exact List.contains_iff_mem.2 hx)
  cases ht : restrict (leaves s) t with
  | none => simp [restrictionAgrees,ht] at hg
  | some u =>
    refine ⟨u,rfl,?_⟩
    apply (sameShape_correct u s).1
    simpa only [restrictionAgrees,ht,hs] using hg

theorem restricted_topology (t s u : Tree) (B : List Nat)
    (ht : restrict (leaves s) t = some u) (hi : RootedIso u s)
    (hsub : B ⊆ leaves s) (hne : B ≠ []) : restrictionAgrees t s B = true := by
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨v,hv⟩ := restriction_exists s B ⟨x,hsub hx,hx⟩
  have his := iso_restrict hi B
  rw [hv] at his
  cases hu : restrict B u with
  | none => simp [hu,OptionIso] at his
  | some w =>
    have htw : restrict B t = some w := (restrict_inside t u (leaves s) B ht hsub).symm.trans hu
    have hwv : RootedIso w v := by simpa only [hu,OptionIso] using his
    simpa only [restrictionAgrees,htw,hv] using (sameShape_correct w v).2 hwv

theorem allGood_completion (t : Tree) (ss : List Tree) (F : List (List Nat))
    (hp : proper (some t) ss = true)
    (hg : ∀ s ∈ ss, targetAgrees (some t) s (leaves s) = true)
    (hF : partitionCheck (leaves t) F = true)
    (href : ∀ B ∈ F, ∃ s ∈ ss, B ⊆ leaves s)
    (he : pairwiseEmbeddings t F = true) : agrees (some t) ss F = true := by
  have hQ := (proper_parts (some t) ss hp).2
  have hRef : Refines F (ss.map leaves) := by
    intro B hB
    obtain ⟨s,hs,hBs⟩ := href B hB
    exact ⟨leaves s,List.mem_map.2 ⟨s,hs,rfl⟩,hBs⟩
  simp only [agrees,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,contained_iff]
  refine ⟨⟨⟨⟨hp,hF⟩,href⟩,he⟩,?_⟩
  intro s hs
  obtain ⟨u,htu,hi⟩ := full_source_iso t s (hg s hs)
  have hFamSub : ∀ B ∈ family (leaves s) F, B ⊆ leaves s :=
    fun B hB => (mem_family B (leaves s) F).1 hB |>.2
  have hpartu := local_partition t u (leaves s) F (ss.map leaves) htu hF hQ hRef
    (List.mem_map.2 ⟨s,hs,rfl⟩)
  have hparts := (partition_labels_congr (leaves u) (leaves s) _ (iso_leaves_mem hi)).1 hpartu
  have hFamE : pairwiseEmbeddings t (family (leaves s) F) = true := by
    apply (pairwise_iff _ _).2
    exact List.Pairwise.filter _ ((pairwise_iff _ _).1 he)
  have heu := (pairwise_transport t u (leaves s) _ htu hFamSub).1 hFamE
  have hes := (iso_pairwise hi _).1 heu
  simp only [sourceCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨hparts,?_⟩,hes⟩
  intro B hB
  have hBF := (mem_family B (leaves s) F).1 hB |>.1
  exact restricted_topology t s u B htu hi (hFamSub B hB)
    (checked_nonempty (leaves t) F hF B hBF)

theorem candidate_agrees (T : Option Tree) (ss : List Tree) (hg : allGood T ss = true) :
    agrees T ss (candidate T ss) = true := by
  obtain ⟨hp,hgood⟩ := allGood_parts T ss hg
  cases T with
  | none => exact (none_agreement ss hp).2.1
  | some t =>
    exact allGood_completion t ss (candidate (some t) ss) hp hgood
      (candidate_partition (some t) ss hp) (candidate_ownership (some t) ss hp)
      (candidate_embeddings t ss hp)

theorem run_sound (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (hr : run T ss = some F) : agrees T ss F = true := by
  unfold run at hr
  split at hr
  · have he : candidate T ss = F := Option.some.inj hr
    rw [←he]
    exact candidate_agrees T ss (by assumption)
  · contradiction

end AllGoodDP
