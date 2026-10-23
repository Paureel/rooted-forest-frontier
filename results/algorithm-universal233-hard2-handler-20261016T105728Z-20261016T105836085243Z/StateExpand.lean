import Expansion

namespace ForestState
open RMAF RestrictionBridge

theorem contracted_no_endpoints (t : Tree) (a b z : Nat) (shape : QuotientShape a b t)
    (nd : (leaves t).Nodup) (hz : z ∉ leaves t) (hza : z ≠ a) (hzb : z ≠ b) :
    a ∉ leaves (contract a b z t) ∧ b ∉ leaves (contract a b z t) := by
  constructor
  · apply List.count_eq_zero.1
    rw [quotient_tree_count t a b z a shape nd hz]
    simp [Ne.symm hza]
  · apply List.count_eq_zero.1
    rw [quotient_tree_count t a b z b shape nd hz]
    simp [Ne.symm hzb]

theorem expanded_block_sub_iff (s : Tree) (C : List Nat) (a b z : Nat)
    (shape : QuotientShape a b s) (nd : (leaves s).Nodup) (hz : z ∉ leaves s)
    (ha : a ∉ C) (hb : b ∉ C) (hza : z ≠ a) (hzb : z ≠ b) :
    expandBlock a b z C ⊆ leaves s ↔ C ⊆ leaves (contract a b z s) := by
  have hh := block_sub_quotient_iff s (expandBlock a b z C) a b z shape nd hz
    (expandBlock_fresh C a b z hza hzb) (expandBlock_saturated C a b z ha hb)
  have hm : ∀ x, x ∈ contractBlock a b z (expandBlock a b z C) ↔ x ∈ C := by
    intro x
    simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 (contract_expandBlock_mask C a b z ha hb hza hzb x)
  rw [List.subset_def,List.subset_def] at hh ⊢
  simpa only [hm] using hh.symm

theorem expanded_block_clear (s : Tree) (C D : List Nat) (a b z : Nat)
    (shape : QuotientShape a b s) (nd : (leaves s).Nodup) (hz : z ∉ leaves s)
    (haC : a ∉ C) (hbC : b ∉ C) (haD : a ∉ D) (hbD : b ∉ D) (hza : z ≠ a) (hzb : z ≠ b) :
    disjointVertices (minimalVertices (expandBlock a b z C) s) (minimalVertices (expandBlock a b z D) s) = true ↔
      disjointVertices (minimalVertices C (contract a b z s)) (minimalVertices D (contract a b z s)) = true := by
  have hh := quotient_tree_clear s (expandBlock a b z C) (expandBlock a b z D) a b z shape nd hz
    (expandBlock_fresh C a b z hza hzb) (expandBlock_fresh D a b z hza hzb)
    (expandBlock_saturated C a b z haC hbC) (expandBlock_saturated D a b z haD hbD)
  have ec := geometry_mask_equal (contract a b z s) (contractBlock a b z (expandBlock a b z C)) C
    (fun x _ => contract_expandBlock_mask C a b z haC hbC hza hzb x)
  have ed := geometry_mask_equal (contract a b z s) (contractBlock a b z (expandBlock a b z D)) D
    (fun x _ => contract_expandBlock_mask D a b z haD hbD hza hzb x)
  simpa only [ec.2,ed.2] using hh

theorem expanded_block_topology (t s : Tree) (C : List Nat) (a b z : Nat)
    (ht : QuotientShape a b t) (hs : QuotientShape a b s)
    (ndt : (leaves t).Nodup) (nds : (leaves s).Nodup) (hzt : z ∉ leaves t) (hzs : z ∉ leaves s)
    (ha : a ∉ C) (hb : b ∉ C) (hza : z ≠ a) (hzb : z ≠ b)
    (h : restrictionAgrees (contract a b z t) (contract a b z s) C = true) :
    restrictionAgrees t s (expandBlock a b z C) = true := by
  apply quotient_topology_reflect t s (expandBlock a b z C) a b z ht hs ndt nds hzt hzs
    (expandBlock_fresh C a b z hza hzb) (expandBlock_saturated C a b z ha hb)
  have et := restrict_mask_equal (contract a b z t) (contractBlock a b z (expandBlock a b z C)) C
    (fun x _ => contract_expandBlock_mask C a b z ha hb hza hzb x)
  have es := restrict_mask_equal (contract a b z s) (contractBlock a b z (expandBlock a b z C)) C
    (fun x _ => contract_expandBlock_mask C a b z ha hb hza hzb x)
  simpa only [restrictionAgrees,et,es] using h

theorem common_cherry_expansion_partition (t : Tree) (G : List (List Nat)) (a b z : Nat)
    (nd : (leaves t).Nodup) (ch : cherry a b t = true) (hz : z ∉ leaves t) (hab : a ≠ b)
    (hG : partitionCheck (leaves (contract a b z t)) G = true) :
    partitionCheck (leaves t) (G.map (expandBlock a b z)) = true := by
  obtain ⟨w,hw⟩ := cherry_at_exists t a b ch
  have hza : z ≠ a := fun he => hz (he ▸ hw.labels.1)
  have hzb : z ≠ b := fun he => hz (he ▸ hw.labels.2)
  have ends := contracted_no_endpoints t a b z (Or.inl ch) nd hz hza hzb
  have ha : ∀ C ∈ G, a ∉ C := fun C hC hm => ends.1 (checked_label _ _ hG hC hm)
  have hb : ∀ C ∈ G, b ∉ C := fun C hC hm => ends.2 (checked_label _ _ hG hC hm)
  have ndc := contraction_nodup t a b z nd ch hz
  apply partition_by_counts _ _ nd
  · intro B hB
    obtain ⟨C,hC,rfl⟩ := List.mem_map.1 hB
    exact expandBlock_nonempty C a b z (checked_nonempty _ _ hG C hC)
  · intro x
    rw [expanded_forest_count G a b z x hab ha hb hza hzb,
      partition_counts _ _ hG ndc z,partition_counts _ _ hG ndc x,
      hw.contract_count z z nd hz,hw.contract_count z x nd hz]
    have hca := nodup_count_one (leaves t) nd a hw.labels.1
    have hcb := nodup_count_one (leaves t) nd b hw.labels.2
    have hcz := List.count_eq_zero.2 hz
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxz : x = z <;> simp_all

theorem common_cherry_expand_agreement (t : Tree) (ss : List Tree) (G : List (List Nat))
    (a b z : Nat) (ready : cherryReady (some t) ss a b z = true)
    (h : agrees (some (contract a b z t)) (ss.map (contract a b z)) G = true) :
    agrees (some t) ss (G.map (expandBlock a b z)) = true := by
  have rr : proper (some t) ss = true ∧ a ≠ b ∧ z ∉ labels (some t) ∧
      cherry a b t = true ∧ ∃ s ∈ ss, cherry a b s = true := by
    simpa [cherryReady,Bool.and_eq_true,List.any_eq_true,and_assoc] using ready
  obtain ⟨s0,hs0,ch0⟩ := rr.2.2.2.2
  have hp := rr.1
  have hab := rr.2.1
  have ch := rr.2.2.2.1
  have hz : z ∉ leaves t := rr.2.2.1
  have nd := (proper_parts (some t) ss hp).1
  have hQ := (proper_parts (some t) ss hp).2
  obtain ⟨w,hw⟩ := cherry_at_exists t a b ch
  have hza : z ≠ a := fun he => hz (he ▸ hw.labels.1)
  have hzb : z ≠ b := fun he => hz (he ▸ hw.labels.2)
  have shape := source_quotient_shape t ss a b hp s0 hs0 ch0
  have nds := proper_source_nodup (some t) ss hp
  have hzs : ∀ s ∈ ss, z ∉ leaves s := by
    intro s hs hm
    exact hz (checked_label (leaves t) (ss.map leaves) hQ (List.mem_map.2 ⟨s,hs,rfl⟩) hm)
  obtain ⟨hpc,hG,href,ht,hsc⟩ := agrees_parts _ _ _ h
  have ends := contracted_no_endpoints t a b z (Or.inl ch) nd hz hza hzb
  have ha : ∀ C ∈ G, a ∉ C := fun C hC hm => ends.1 (checked_label _ _ hG hC hm)
  have hb : ∀ C ∈ G, b ∉ C := fun C hC hm => ends.2 (checked_label _ _ hG hC hm)
  have hF := common_cherry_expansion_partition t G a b z nd ch hz hab hG
  apply agrees_from_checks t ss _ hp hF
  · intro B hB
    obtain ⟨C,hC,rfl⟩ := List.mem_map.1 hB
    obtain ⟨u,hu,sub⟩ := href C hC
    obtain ⟨s,hs,rfl⟩ := List.mem_map.1 hu
    exact ⟨s,hs,(expanded_block_sub_iff s C a b z (shape s hs) (nds s hs) (hzs s hs)
      (ha C hC) (hb C hC) hza hzb).mpr sub⟩
  · apply pairwise_of_distinct t _ (checked_forest_nodup (leaves t) _ hF)
    intro B hB D hD hne
    obtain ⟨C,hC,rfl⟩ := List.mem_map.1 hB
    obtain ⟨E,hE,rfl⟩ := List.mem_map.1 hD
    have hCE : C ≠ E := by intro he; subst E; exact hne rfl
    apply (expanded_block_clear t C E a b z (Or.inl ch) nd hz (ha C hC) (hb C hC)
      (ha E hE) (hb E hE) hza hzb).mpr
    exact pairwise_distinct_members (contract a b z t) G ht C E hC hE hCE
  · intro s hs B hB sub
    obtain ⟨C,hC,rfl⟩ := List.mem_map.1 hB
    have subc := (expanded_block_sub_iff s C a b z (shape s hs) (nds s hs) (hzs s hs)
      (ha C hC) (hb C hC) hza hzb).mp sub
    exact expanded_block_topology t s C a b z (Or.inl ch) (shape s hs) nd (nds s hs) hz (hzs s hs)
      (ha C hC) (hb C hC) hza hzb
      (agrees_block_topology (contract a b z t) (ss.map (contract a b z)) G h
        (contract a b z s) (List.mem_map.2 ⟨s,hs,rfl⟩) C hC subc)
  · intro s hs B hB D hD subB subD hne
    obtain ⟨C,hC,rfl⟩ := List.mem_map.1 hB
    obtain ⟨E,hE,rfl⟩ := List.mem_map.1 hD
    have subC := (expanded_block_sub_iff s C a b z (shape s hs) (nds s hs) (hzs s hs)
      (ha C hC) (hb C hC) hza hzb).mp subB
    have subE := (expanded_block_sub_iff s E a b z (shape s hs) (nds s hs) (hzs s hs)
      (ha E hE) (hb E hE) hza hzb).mp subD
    have hCE : C ≠ E := by intro he; subst E; exact hne rfl
    apply (expanded_block_clear s C E a b z (shape s hs) (nds s hs) (hzs s hs)
      (ha C hC) (hb C hC) (ha E hE) (hb E hE) hza hzb).mpr
    exact agrees_block_source_clear (contract a b z t) (ss.map (contract a b z)) G h
      (contract a b z s) (List.mem_map.2 ⟨s,hs,rfl⟩) C E hC hE subC subE hCE

theorem common_cherry_decision_reverse (t : Tree) (ss : List Tree) (a b z q : Nat)
    (ready : cherryReady (some t) ss a b z = true)
    (h : feasible (some (contract a b z t)) (ss.map (contract a b z)) q) :
    feasible (some t) ss q := by
  obtain ⟨G,hG,hcost⟩ := h
  refine ⟨G.map (expandBlock a b z),common_cherry_expand_agreement t ss G a b z ready hG,?_⟩
  simpa [additionalCost] using hcost

theorem common_cherry_decision_equivalence (t : Tree) (ss : List Tree) (a b z q : Nat)
    (ready : cherryReady (some t) ss a b z = true) :
    feasible (some t) ss q ↔ feasible (some (contract a b z t)) (ss.map (contract a b z)) q := by
  exact ⟨common_cherry_decision_forward t ss a b z q ready,
    common_cherry_decision_reverse t ss a b z q ready⟩

theorem common_cherry_expand_exact_cost (ss : List Tree) (G : List (List Nat)) (a b z : Nat) :
    additionalCost ss (G.map (expandBlock a b z)) = additionalCost (ss.map (contract a b z)) G := by
  simp [additionalCost]

theorem common_cherry_state_decision_equivalence (T : Option Tree) (ss : List Tree) (a b z q : Nat)
    (ready : cherryReady T ss a b z = true) :
    feasible T ss q ↔ feasible (T.map (contract a b z)) (ss.map (contract a b z)) q := by
  cases T with
  | none => simp [cherryReady] at ready
  | some t => exact common_cherry_decision_equivalence t ss a b z q ready

theorem common_cherry_state_strict_decrease (T : Option Tree) (ss : List Tree) (a b z : Nat)
    (ready : cherryReady T ss a b z = true) :
    (labels (T.map (contract a b z))).length + 1 = (labels T).length := by
  cases T with
  | none => simp [cherryReady] at ready
  | some t => exact cherry_ready_strict_decrease t ss a b z ready

end ForestState
