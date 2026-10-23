import GroupForwardProof
namespace ForestGroups
open RMAF RestrictionBridge ForestState

theorem flatmap_one {α β : Type} [DecidableEq α] (Q : List α) (U : α) (H : α → List β)
    (hn : Q.Nodup) (hU : U ∈ Q) (hz : ∀ V ∈ Q, V ≠ U → H V = []) :
    Q.flatMap H = H U := by
  induction Q with
  | nil => simp at hU
  | cons V Q ih =>
    have nd := List.nodup_cons.1 hn
    by_cases eq : V = U
    · subst V
      have z : Q.flatMap H = [] := List.flatMap_eq_nil_iff.2 (by
        intro W hw
        exact hz W (by simp [hw]) (by intro eq; subst W; exact nd.1 hw))
      simp [z]
    · have hu : U ∈ Q := by
        rcases List.mem_cons.1 hU with he | hm
        · exact False.elim (eq he.symm)
        · exact hm
      simp only [List.flatMap_cons,hz V (by simp) eq,List.nil_append]
      exact ih nd.2 hu (fun W hw => hz W (by simp [hw]))

theorem family_concat_owned (L : List Nat) (Q : List (List Nat))
    (G : List Nat → List (List Nat)) (U S : List Nat)
    (hq : partitionCheck L Q = true) (hU : U ∈ Q) (hSU : S ⊆ U)
    (hp : ∀ V ∈ Q, partitionCheck V (G V) = true) :
    family S (Q.flatMap G) = family S (G U) := by
  simp only [family,List.filter_flatMap]
  apply flatmap_one Q U (fun V => (G V).filter (contained · S))
    (checked_family_nodup L Q hq) hU
  intro V hV hne
  apply List.filter_eq_nil_iff.2
  intro B hB hc
  have hBS := (contained_iff B S).1 hc
  have hBU := List.Subset.trans hBS hSU
  have hBV : B ⊆ V := fun x hx => checked_label V (G V) (hp V hV) hB hx
  exact hne (block_group_owner L Q hq V U B hV hU
    (checked_nonempty V (G V) (hp V hV) B hB) hBV hBU)

theorem concat_pairwise_cross (t : Tree) (Q : List (List Nat))
    (G : List Nat → List (List Nat)) (hn : Q.Nodup)
    (hl : ∀ U ∈ Q, pairwiseEmbeddings t (G U) = true)
    (hc : ∀ U ∈ Q, ∀ V ∈ Q, U ≠ V → ∀ B ∈ G U, ∀ C ∈ G V,
      Clear (minimalVertices B t) (minimalVertices C t)) :
    pairwiseEmbeddings t (Q.flatMap G) = true := by
  apply (pairwise_iff t _).2
  induction Q with
  | nil => simp
  | cons U Q ih =>
    have hnd := List.nodup_cons.1 hn
    rw [List.flatMap_cons,List.pairwise_append]
    refine ⟨(pairwise_iff t (G U)).1 (hl U (by simp)),
      ih hnd.2 (fun V hv => hl V (by simp [hv]))
        (fun V hv W hw => hc V (by simp [hv]) W (by simp [hw])),?_⟩
    intro B hb C hc0
    obtain ⟨V,hV,hC⟩ := List.mem_flatMap.1 hc0
    exact hc U (by simp) V (by simp [hV])
      (by intro eq; subst V; exact hnd.1 hV) B hb C hC

theorem local_partition_groups (T : Option Tree) (ss : List Tree) (Q : List (List Nat))
    (G : List Nat → List (List Nat)) (hp : proper T ss = true)
    (hq : partitionCheck (labels T) Q = true)
    (ha : ∀ U ∈ Q, agrees (localTarget T U) (owned ss U) (G U) = true) :
    ∀ U ∈ Q, partitionCheck U (G U) = true := by
  intro U hU
  obtain ⟨t,u,ht,hu,he,hperm⟩ := group_target T ss Q hp hq U hU
  have hf := (agrees_parts _ _ _ (ha U hU)).2.1
  have hf' : partitionCheck (leaves u) (G U) = true := by simpa [he,labels] using hf
  exact (partition_labels_congr (leaves u) U (G U) (fun x => hperm.mem_iff)).1 hf'

/-- Reverse reconstruction from actual local forest-state agreements. The sole
cross-group geometry assumption concerns current individual source trees. It
permits arbitrarily overlapping target embeddings within a group. -/
theorem reverse_reconstruction (T : Option Tree) (ss : List Tree) (Q : List (List Nat))
    (G : List Nat → List (List Nat)) (hp : proper T ss = true)
    (hq : partitionCheck (labels T) Q = true) (own : Owns ss Q)
    (cross : CrossClear T ss Q)
    (ha : ∀ U ∈ Q, agrees (localTarget T U) (owned ss U) (G U) = true) :
    agrees T ss (Q.flatMap G) = true := by
  have pg := local_partition_groups T ss Q G hp hq ha
  cases T with
  | none =>
    have eqQ : Q = [] := checked_empty Q hq
    have eqss : ss = [] := by
      have hh := checked_empty (ss.map leaves) (proper_parts _ _ hp).2
      simpa using hh
    subst Q; subst ss
    simp [agrees,proper,labels,partitionCheck,targetEmbeddings]
  | some t =>
    have hpart := checked_concat (leaves t) Q G hq pg
    have origE : ∀ U ∈ Q, pairwiseEmbeddings t (G U) = true := by
      intro U hU
      obtain ⟨t0,u,ht,hu,he,hperm⟩ := group_target (some t) ss Q hp hq U hU
      have ht0 : t = t0 := Option.some.inj ht
      subst t0
      have hE := (agrees_parts _ _ _ (ha U hU)).2.2.2.1
      have hEu : pairwiseEmbeddings u (G U) = true := by simpa [he,targetEmbeddings] using hE
      exact (pairwise_transport t u U (G U) hu (by
        intro B hb x hx; exact checked_label U (G U) (pg U hU) hb hx)).2 hEu
    have href : ∀ B ∈ Q.flatMap G, ∃ s ∈ ss, B ⊆ leaves s := by
      intro B hB
      obtain ⟨U,hU,hB⟩ := List.mem_flatMap.1 hB
      obtain ⟨s,hs,hBs⟩ := (agrees_parts _ _ _ (ha U hU)).2.2.1 B hB
      exact ⟨s,((mem_owned s ss U).1 hs).1,hBs⟩
    have hcross : ∀ U ∈ Q, ∀ V ∈ Q, U ≠ V → ∀ B ∈ G U, ∀ C ∈ G V,
        Clear (minimalVertices B t) (minimalVertices C t) := by
      intro U hU V hV hne B hB C hC
      obtain ⟨s,hs,hBs⟩ := (agrees_parts _ _ _ (ha U hU)).2.2.1 B hB
      obtain ⟨r,hr,hCr⟩ := (agrees_parts _ _ _ (ha V hV)).2.2.1 C hC
      intro v hv hw
      exact cross t rfl U hU V hV hne s hs r hr v
        (VertexGeometry.executable_span_monotone t B (leaves s) (fun _ hx => hBs hx) v hv)
        (VertexGeometry.executable_span_monotone t C (leaves r) (fun _ hx => hCr hx) v hw)
    have hsource : ∀ s ∈ ss, sourceCheck (some t) (Q.flatMap G) s = true := by
      intro s hs
      obtain ⟨U,hU,hsU⟩ := own s hs
      obtain ⟨t0,u,ht,hu,he,hperm⟩ := group_target (some t) ss Q hp hq U hU
      have htt : t = t0 := Option.some.inj ht
      subst t0
      have hS := (agrees_parts _ _ _ (ha U hU)).2.2.2.2 s ((mem_owned s ss U).2 ⟨hs,hsU⟩)
      have hS0 : sourceCheck (some u) (G U) s = true := by simpa [he] using hS
      rw [source_check_transport t u s U (G U) hu hsU] at hS0
      simpa only [sourceCheck,family_concat_owned (leaves t) Q G U (leaves s) hq hU hsU pg] using hS0
    simp only [agrees,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,contained_iff]
    exact ⟨⟨⟨⟨hp,hpart⟩,href⟩,
      concat_pairwise_cross t Q G (checked_family_nodup _ _ hq) origE hcross⟩,hsource⟩
end ForestGroups
