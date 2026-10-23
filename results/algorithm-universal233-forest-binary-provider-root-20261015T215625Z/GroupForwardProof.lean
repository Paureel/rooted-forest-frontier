import GroupDefs
namespace ForestGroups
open RMAF RestrictionBridge ForestState

theorem source_check_transport (t u s : Tree) (U : List Nat) (F : List (List Nat))
    (hu : restrict U t = some u) (hsU : leaves s ⊆ U) :
    sourceCheck (some u) F s = sourceCheck (some t) F s := by
  have eqon : ∀ B ∈ family (leaves s) F, targetAgrees (some u) s B = targetAgrees (some t) s B := by
    intro B hB
    have hBU := List.Subset.trans ((mem_family B (leaves s) F).1 hB).2 hsU
    simp only [targetAgrees,restrictionAgrees,restrict_inside t u U B hu hBU]
  have aux : ∀ (L : List (List Nat)),
      (∀ B ∈ L, targetAgrees (some u) s B = targetAgrees (some t) s B) →
      L.all (targetAgrees (some u) s) = L.all (targetAgrees (some t) s) := by
    intro L h
    induction L with
    | nil => rfl
    | cons B L ih =>
      simp only [List.all_cons,h B (by simp),ih (fun C hc => h C (by simp [hc]))]
  simp only [sourceCheck,aux _ eqon]

theorem local_forward (T : Option Tree) (ss : List Tree) (Q F : List (List Nat))
    (ha : agrees T ss F = true) (hq : partitionCheck (labels T) Q = true)
    (own : Owns ss Q) (U : List Nat) (hU : U ∈ Q) :
    agrees (localTarget T U) (owned ss U) (family U F) = true := by
  obtain ⟨hp,hF,href,hE,hS⟩ := agrees_parts T ss F ha
  obtain ⟨t,u,ht,hu,he,hperm⟩ := group_target T ss Q hp hq U hU
  subst T
  have hpart := local_partition t u U F Q hu hF hq (state_refines _ _ _ _ ha own) hU
  have hsub : ∀ B ∈ family U F, B ⊆ U := fun B hb => ((mem_family B U F).1 hb).2
  have hsource : ∀ s ∈ owned ss U, sourceCheck (some u) (family U F) s = true := by
    intro s hs
    obtain ⟨hss,hsU⟩ := (mem_owned s ss U).1 hs
    rw [source_check_transport t u s U (family U F) hu hsU]
    simpa only [sourceCheck,family_nested (leaves s) U F hsU] using hS s hss
  rw [he]
  simp only [agrees,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,contained_iff]
  refine ⟨⟨⟨⟨by simpa only [he] using local_proper (some t) ss Q hp hq own U hU,hpart⟩,?_⟩,?_⟩,hsource⟩
  · intro B hB
    obtain ⟨hBF,hBU⟩ := (mem_family B U F).1 hB
    obtain ⟨s,hs,hBs⟩ := href B hBF
    obtain ⟨V,hV,hsV⟩ := own s hs
    have eq := block_group_owner (leaves t) Q hq U V B hU hV
      (checked_nonempty (leaves t) F hF B hBF) hBU (List.Subset.trans hBs hsV)
    exact ⟨s,(mem_owned s ss U).2 ⟨hs,by simpa [eq] using hsV⟩,hBs⟩
  · exact (pairwise_transport t u U (family U F) hu hsub).1
      (pairwise_filter t F (contained · U) hE)

/-- Every original literal state agreement decomposes. Cross-clear is unnecessary
in this forward direction. Source components are retained literally. -/
theorem forward_decomposition (T : Option Tree) (ss : List Tree) (Q F : List (List Nat))
    (ha : agrees T ss F = true) (hq : partitionCheck (labels T) Q = true)
    (own : Owns ss Q) :
    ∀ U ∈ Q, agrees (localTarget T U) (owned ss U) (family U F) = true :=
  fun U hU => local_forward T ss Q F ha hq own U hU
end ForestGroups
