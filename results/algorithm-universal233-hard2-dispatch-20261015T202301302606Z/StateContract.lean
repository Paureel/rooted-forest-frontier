import QuotientTopology

namespace ForestState
open RMAF RestrictionBridge

def QuotientShape (a b : Nat) (t : Tree) : Prop :=
  cherry a b t = true ∨ (a ∉ leaves t ∧ b ∉ leaves t)

theorem source_quotient_shape (t : Tree) (ss : List Tree) (a b : Nat)
    (hp : proper (some t) ss = true) (s0 : Tree) (hs0 : s0 ∈ ss)
    (ch0 : cherry a b s0 = true) (s : Tree) (hs : s ∈ ss) : QuotientShape a b s := by
  obtain ⟨w,hw⟩ := cherry_at_exists s0 a b ch0
  by_cases ha : a ∈ leaves s
  · have he := proper_source_owner (some t) ss hp s s0 hs hs0 a ha hw.labels.1
    exact Or.inl (he ▸ ch0)
  · refine Or.inr ⟨ha,?_⟩
    intro hb
    have he := proper_source_owner (some t) ss hp s s0 hs hs0 b hb hw.labels.2
    exact ha (he ▸ hw.labels.1)

theorem quotient_shape_coalesced (s : Tree) (a b : Nat) (h : QuotientShape a b s) :
    a ∈ leaves s ↔ b ∈ leaves s := by
  rcases h with ch | ⟨ha,hb⟩
  · obtain ⟨w,hw⟩ := cherry_at_exists s a b ch
    exact ⟨fun _ => hw.labels.2,fun _ => hw.labels.1⟩
  · simp [ha,hb]

theorem quotient_tree_count (s : Tree) (a b z x : Nat) (h : QuotientShape a b s)
    (nd : (leaves s).Nodup) (hz : z ∉ leaves s) :
    (leaves (contract a b z s)).count x =
      if x = z then (leaves s).count a else if x = a ∨ x = b then 0 else (leaves s).count x := by
  rcases h with ch | ⟨ha,hb⟩
  · obtain ⟨w,hw⟩ := cherry_at_exists s a b ch
    rw [hw.contract_count z x nd hz,nodup_count_one (leaves s) nd a hw.labels.1]
  · rw [contract_absent s a b z ha]
    have hca := List.count_eq_zero.2 ha
    have hcb := List.count_eq_zero.2 hb
    have hcz := List.count_eq_zero.2 hz
    by_cases hxz : x = z <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all

theorem quotient_tree_mem (s : Tree) (a b z x : Nat) (h : QuotientShape a b s)
    (nd : (leaves s).Nodup) (hz : z ∉ leaves s) :
    x ∈ leaves (contract a b z s) ↔
      (x = z ∧ a ∈ leaves s) ∨ (x ≠ z ∧ x ≠ a ∧ x ≠ b ∧ x ∈ leaves s) := by
  rw [←List.count_pos_iff,quotient_tree_count s a b z x h nd hz]
  by_cases hxz : x = z <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    simp_all [List.count_pos_iff]

theorem contractBlock_mem (B : List Nat) (a b z x : Nat) (hz : z ∉ B)
    (sat : a ∈ B ↔ b ∈ B) :
    x ∈ contractBlock a b z B ↔
      (x = z ∧ a ∈ B) ∨ (x ≠ z ∧ x ≠ a ∧ x ≠ b ∧ x ∈ B) := by
  by_cases ha : a ∈ B
  · have hb := sat.mp ha
    have hza : z ≠ a := by intro he; subst z; exact hz ha
    have hzb : z ≠ b := by intro he; subst z; exact hz hb
    by_cases hxz : x = z <;> simp_all [contractBlock,and_assoc,and_comm,and_left_comm]
  · have hb : b ∉ B := fun hm => ha (sat.mpr hm)
    by_cases hxz : x = z <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp_all [contractBlock]

theorem block_sub_quotient_iff (s : Tree) (B : List Nat) (a b z : Nat)
    (h : QuotientShape a b s) (nd : (leaves s).Nodup) (hz : z ∉ leaves s)
    (hzB : z ∉ B) (sat : a ∈ B ↔ b ∈ B) :
    contractBlock a b z B ⊆ leaves (contract a b z s) ↔ B ⊆ leaves s := by
  constructor
  · intro sub x hx
    by_cases hxa : x = a
    · subst x
      have hm := sub ((contractBlock_z B a b z hzB).2 hx)
      exact ((quotient_tree_mem s a b z z h nd hz).1 hm).resolve_right (by simp) |>.2
    · by_cases hxb : x = b
      · subst x
        have ha := sat.mpr hx
        have hm := sub ((contractBlock_z B a b z hzB).2 ha)
        have has := ((quotient_tree_mem s a b z z h nd hz).1 hm).resolve_right (by simp) |>.2
        exact (quotient_shape_coalesced s a b h).mp has
      · have hxz : x ≠ z := by intro he; subst x; exact hzB hx
        have hm := sub ((contractBlock_mem B a b z x hzB sat).2 (Or.inr ⟨hxz,hxa,hxb,hx⟩))
        rcases (quotient_tree_mem s a b z x h nd hz).1 hm with ⟨he,_⟩ | ⟨_,_,_,hs⟩
        · exact False.elim (hxz he)
        · exact hs
  · intro sub x hx
    apply (quotient_tree_mem s a b z x h nd hz).2
    rcases (contractBlock_mem B a b z x hzB sat).1 hx with ⟨he,ha⟩ | ⟨hxz,hxa,hxb,hxB⟩
    · exact Or.inl ⟨he,sub ha⟩
    · exact Or.inr ⟨hxz,hxa,hxb,sub hxB⟩

theorem quotient_tree_restriction (s : Tree) (B : List Nat) (a b z : Nat)
    (h : QuotientShape a b s) (nd : (leaves s).Nodup) (hz : z ∉ leaves s)
    (hzB : z ∉ B) (sat : a ∈ B ↔ b ∈ B) :
    restrict (contractBlock a b z B) (contract a b z s) =
      (restrict B s).map (contract a b z) := by
  rcases h with ch | ⟨ha,hb⟩
  · obtain ⟨w,hw⟩ := cherry_at_exists s a b ch
    exact hw.contract_restriction z B nd hz hzB sat
  · rw [contract_absent s a b z ha,
      ←restrict_mask_equal s B (contractBlock a b z B) (contracted_mask_absent s B a b z ha hb hz)]
    cases rr : restrict B s with
    | none => rfl
    | some u =>
      have hu : a ∉ leaves u := by intro hm; exact ha ((restricted_labels_exact s u B rr).1 hm).1
      simp [contract_absent u a b z hu]

theorem quotient_tree_clear (s : Tree) (B C : List Nat) (a b z : Nat)
    (h : QuotientShape a b s) (nd : (leaves s).Nodup) (hz : z ∉ leaves s)
    (hzB : z ∉ B) (hzC : z ∉ C) (satB : a ∈ B ↔ b ∈ B) (satC : a ∈ C ↔ b ∈ C) :
    disjointVertices (minimalVertices B s) (minimalVertices C s) = true ↔
      disjointVertices (minimalVertices (contractBlock a b z B) (contract a b z s))
        (minimalVertices (contractBlock a b z C) (contract a b z s)) = true := by
  rw [clear_iff,clear_iff]
  rcases h with ch | ⟨ha,hb⟩
  · obtain ⟨w,hw⟩ := cherry_at_exists s a b ch
    exact (hw.quotient_geometry z B C nd hz hzB hzC satB satC).2.2.2.2
  · have eB := geometry_mask_equal s B (contractBlock a b z B) (contracted_mask_absent s B a b z ha hb hz)
    have eC := geometry_mask_equal s C (contractBlock a b z C) (contracted_mask_absent s C a b z ha hb hz)
    rw [contract_absent s a b z ha,eB.2,eC.2]

theorem quotient_pairwise (s : Tree) (F : List (List Nat)) (a b z : Nat)
    (h : QuotientShape a b s) (nd : (leaves s).Nodup) (hz : z ∉ leaves s)
    (hzF : ∀ B ∈ F, z ∉ B) (sat : Coalesced F a b) (hp : pairwiseEmbeddings s F = true) :
    pairwiseEmbeddings (contract a b z s) (F.map (contractBlock a b z)) = true := by
  induction F with
  | nil => rfl
  | cons B F ih =>
    have old : (∀ C ∈ F, disjointVertices (minimalVertices B s) (minimalVertices C s) = true) ∧
        pairwiseEmbeddings s F = true := by simpa [pairwiseEmbeddings,List.all_eq_true] using hp
    simp only [List.map_cons,pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true]
    refine ⟨?_,ih (fun C hC => hzF C (by simp [hC])) (fun C hC => sat C (by simp [hC])) old.2⟩
    intro D hD
    obtain ⟨C,hC,rfl⟩ := List.mem_map.1 hD
    exact (quotient_tree_clear s B C a b z h nd hz (hzF B (by simp)) (hzF C (by simp [hC]))
      (sat B (by simp)) (sat C (by simp [hC]))).mp (old.1 C hC)

theorem quotient_topology (t s : Tree) (B : List Nat) (a b z : Nat)
    (ht : QuotientShape a b t) (hs : QuotientShape a b s)
    (ndt : (leaves t).Nodup) (nds : (leaves s).Nodup)
    (hzt : z ∉ leaves t) (hzs : z ∉ leaves s) (hzB : z ∉ B) (sat : a ∈ B ↔ b ∈ B)
    (h : restrictionAgrees t s B = true) :
    restrictionAgrees (contract a b z t) (contract a b z s) (contractBlock a b z B) = true := by
  simp only [restrictionAgrees,quotient_tree_restriction t B a b z ht ndt hzt hzB sat,
    quotient_tree_restriction s B a b z hs nds hzs hzB sat]
  cases rt : restrict B t with
  | none => simp [restrictionAgrees,rt] at h
  | some u =>
    cases rs : restrict B s with
    | none => simp [restrictionAgrees,rs] at h
    | some v =>
      have iso : RootedIso u v := (sameShape_correct _ _).1 (by simpa [restrictionAgrees,rt,rs] using h)
      exact (sameShape_correct _ _).2 (contract_preserves_iso a b z iso)

theorem quotient_source_flatten_counts (ss : List Tree) (a b z : Nat)
    (shape : ∀ s ∈ ss, QuotientShape a b s) (nd : ∀ s ∈ ss, (leaves s).Nodup)
    (hz : ∀ s ∈ ss, z ∉ leaves s) (x : Nat) :
    (((ss.map (contract a b z)).map leaves).flatten).count x =
      (((ss.map leaves).map (contractBlock a b z)).flatten).count x := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have hi := ih (fun u hu => shape u (by simp [hu])) (fun u hu => nd u (by simp [hu]))
      (fun u hu => hz u (by simp [hu]))
    simp only [List.map_cons,List.flatten_cons,List.count_append,hi,
      quotient_tree_count s a b z x (shape s (by simp)) (nd s (by simp)) (hz s (by simp)),
      contractBlock_count (leaves s) a b z x (nd s (by simp)) (hz s (by simp))
        (quotient_shape_coalesced s a b (shape s (by simp)))]

theorem contraction_proper (t : Tree) (ss : List Tree) (a b z : Nat)
    (hp : proper (some t) ss = true) (ch : cherry a b t = true) (hz : z ∉ leaves t)
    (s0 : Tree) (hs0 : s0 ∈ ss) (ch0 : cherry a b s0 = true) :
    proper (some (contract a b z t)) (ss.map (contract a b z)) = true := by
  have nd := (proper_parts (some t) ss hp).1
  have hQ := (proper_parts (some t) ss hp).2
  have shape := source_quotient_shape t ss a b hp s0 hs0 ch0
  have nds := proper_source_nodup (some t) ss hp
  have hzs : ∀ s ∈ ss, z ∉ leaves s := by
    intro s hs hm
    exact hz (checked_label (leaves t) (ss.map leaves) hQ (List.mem_map.2 ⟨s,hs,rfl⟩) hm)
  obtain ⟨w,hw⟩ := cherry_at_exists s0 a b ch0
  have satQ := together_coalesced (leaves t) (ss.map leaves) a b hQ (leaves s0)
    (List.mem_map.2 ⟨s0,hs0,rfl⟩) hw.labels.1 hw.labels.2
  have newQ := contraction_partition t (ss.map leaves) a b z nd ch hz hQ satQ
  have newnd := contraction_nodup t a b z nd ch hz
  simp only [proper,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨newnd,partition_by_counts _ _ newnd ?_ ?_⟩
  · intro B hB
    obtain ⟨s,hs,rfl⟩ := List.mem_map.1 hB
    exact leaves_nonempty s
  · intro x
    rw [quotient_source_flatten_counts ss a b z shape nds hzs x]
    exact partition_counts _ _ newQ newnd x

theorem common_cherry_contract_agreement (t : Tree) (ss : List Tree) (F : List (List Nat))
    (a b z : Nat) (h : agrees (some t) ss F = true)
    (ready : cherryReady (some t) ss a b z = true) (sat : Coalesced F a b) :
    agrees (some (contract a b z t)) (ss.map (contract a b z))
      (F.map (contractBlock a b z)) = true := by
  obtain ⟨hp,hF,href,ht,hs⟩ := agrees_parts (some t) ss F h
  have rr : proper (some t) ss = true ∧ a ≠ b ∧ z ∉ labels (some t) ∧
      cherry a b t = true ∧ ∃ s ∈ ss, cherry a b s = true := by
    simpa [cherryReady,Bool.and_eq_true,List.any_eq_true,and_assoc] using ready
  obtain ⟨s0,hs0,ch0⟩ := rr.2.2.2.2
  have ch := rr.2.2.2.1
  have hz : z ∉ leaves t := rr.2.2.1
  have nd := (proper_parts (some t) ss hp).1
  have hQ := (proper_parts (some t) ss hp).2
  have shape := source_quotient_shape t ss a b hp s0 hs0 ch0
  have nds := proper_source_nodup (some t) ss hp
  have hzs : ∀ s ∈ ss, z ∉ leaves s := by
    intro s hs hm
    exact hz (checked_label (leaves t) (ss.map leaves) hQ (List.mem_map.2 ⟨s,hs,rfl⟩) hm)
  have hzF : ∀ B ∈ F, z ∉ B := fun B hB hm => hz (checked_label (leaves t) F hF hB hm)
  apply agrees_from_checks _ _ _ (contraction_proper t ss a b z hp ch hz s0 hs0 ch0)
    (contraction_partition t F a b z nd ch hz hF sat)
  · intro D hD
    obtain ⟨B,hB,rfl⟩ := List.mem_map.1 hD
    obtain ⟨s,hs,sub⟩ := href B hB
    exact ⟨contract a b z s,List.mem_map.2 ⟨s,hs,rfl⟩,
      (block_sub_quotient_iff s B a b z (shape s hs) (nds s hs) (hzs s hs) (hzF B hB) (sat B hB)).mpr sub⟩
  · exact quotient_pairwise t F a b z (Or.inl ch) nd hz hzF sat ht
  · intro s' hs' D hD sub
    obtain ⟨s,hs,rfl⟩ := List.mem_map.1 hs'
    obtain ⟨B,hB,rfl⟩ := List.mem_map.1 hD
    have oldsub := (block_sub_quotient_iff s B a b z (shape s hs) (nds s hs) (hzs s hs)
      (hzF B hB) (sat B hB)).mp sub
    exact quotient_topology t s B a b z (Or.inl ch) (shape s hs) nd (nds s hs) hz (hzs s hs)
      (hzF B hB) (sat B hB) (agrees_block_topology t ss F h s hs B hB oldsub)
  · intro s' hs' D hD E hE subD subE hne
    obtain ⟨s,hs,rfl⟩ := List.mem_map.1 hs'
    obtain ⟨B,hB,rfl⟩ := List.mem_map.1 hD
    obtain ⟨C,hC,rfl⟩ := List.mem_map.1 hE
    have oldB := (block_sub_quotient_iff s B a b z (shape s hs) (nds s hs) (hzs s hs)
      (hzF B hB) (sat B hB)).mp subD
    have oldC := (block_sub_quotient_iff s C a b z (shape s hs) (nds s hs) (hzs s hs)
      (hzF C hC) (sat C hC)).mp subE
    have oldne : B ≠ C := by intro he; subst C; exact hne rfl
    exact (quotient_tree_clear s B C a b z (shape s hs) (nds s hs) (hzs s hs)
      (hzF B hB) (hzF C hC) (sat B hB) (sat C hC)).mp
      (agrees_block_source_clear t ss F h s hs B C hB hC oldB oldC oldne)

theorem common_cherry_decision_forward (t : Tree) (ss : List Tree) (a b z q : Nat)
    (ready : cherryReady (some t) ss a b z = true) (h : feasible (some t) ss q) :
    feasible (some (contract a b z t)) (ss.map (contract a b z)) q := by
  obtain ⟨F,hF,hcost⟩ := h
  have rr : proper (some t) ss = true ∧ a ≠ b ∧ z ∉ labels (some t) ∧
      cherry a b t = true ∧ ∃ s ∈ ss, cherry a b s = true := by
    simpa [cherryReady,Bool.and_eq_true,List.any_eq_true,and_assoc] using ready
  obtain ⟨G,hG,hlen,B,hB,haB,hbB⟩ := common_cherry_no_larger t ss F a b hF rr.2.2.2.1 rr.2.2.2.2
  have sat := together_coalesced (leaves t) G a b (agrees_parts (some t) ss G hG).2.1 B hB haB hbB
  refine ⟨G.map (contractBlock a b z),common_cherry_contract_agreement t ss G a b z hG ready sat,?_⟩
  rw [contraction_additional_cost]
  simp only [additionalCost] at hcost ⊢
  omega

end ForestState
