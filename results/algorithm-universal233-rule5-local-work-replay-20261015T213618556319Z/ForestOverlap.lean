import ForestReplace
namespace GenericForest
open RMAF RestrictionBridge ForestState OutputState ForestGroups VertexGeometry
open Universal233 Universal233.CoreProgram Universal233.Assembly Universal233.CutRealization
open Universal233.SourceCoverage Universal233.WholeSourceMass

-- Same finite-count argument as the completed state-cherry ownership lemma.
theorem source_owner_count (ss : List Tree) (x : Nat)
    (hc : (ss.map leaves).flatten.count x = 1)
    (s u : Tree) (hs : s ∈ ss) (hu : u ∈ ss)
    (hxs : x ∈ leaves s) (hxu : x ∈ leaves u) : s = u := by
  induction ss with
  | nil => simp at hs
  | cons v vs ih =>
    simp only [List.map_cons,List.flatten_cons,List.count_append] at hc
    rcases List.mem_cons.1 hs with he | hst
    · subst s
      rcases List.mem_cons.1 hu with he | hut
      · exact he.symm
      · have hpos := List.count_pos_iff.2 hxs
        have hp := List.count_pos_iff.2 (List.mem_flatten.2
          ⟨leaves u,List.mem_map.2 ⟨u,hut,rfl⟩,hxu⟩)
        omega
    · rcases List.mem_cons.1 hu with he | hut
      · subst u
        have hpos := List.count_pos_iff.2 hxu
        have hp := List.count_pos_iff.2 (List.mem_flatten.2
          ⟨leaves s,List.mem_map.2 ⟨s,hst,rfl⟩,hxs⟩)
        omega
      · have hn : x ∉ leaves v := by
          intro hxv
          have hpos := List.count_pos_iff.2 hxv
          have hp := List.count_pos_iff.2 (List.mem_flatten.2
            ⟨leaves s,List.mem_map.2 ⟨s,hst,rfl⟩,hxs⟩)
          omega
        exact ih (by simpa [List.count_eq_zero.2 hn] using hc) hst hut

theorem source_owner (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (s r : Tree) (hs : s ∈ ss) (hr : r ∈ ss) (x : Nat)
    (hxs : x ∈ leaves s) (hxr : x ∈ leaves r) : s = r := by
  have hpart := (proper_parts _ _ hp).2
  have hx := (proper_source_labels t ss hp s hs).2 hxs
  exact source_owner_count ss x (checked_count _ _ hpart hx) s r hs hr hxs hxr

theorem source_labels_disjoint (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (s r : Tree) (hs : s ∈ ss) (hr : r ∈ ss) (hne : s ≠ r) :
    ∀ x, x ∈ leaves s → x ∈ leaves r → False := by
  intro x hxs hxr
  exact hne (source_owner t ss hp s r hs hr x hxs hxr)

theorem state_two_parent_ownership (t : Tree) (ss : List Tree) (F : Forest)
    (ha : agrees (some t) ss F = true) (s r : Tree) (hs : s ∈ ss) (hr : r ∈ ss)
    (hne : s ≠ r) (v : RMAF.Vertex) :
    Clears t (family (leaves s) F) v ∨ Clears t (family (leaves r) F) v := by
  classical
  obtain ⟨hp,hF,hown,hE,hS⟩ := agrees_parts _ _ _ ha
  by_cases hclear : Clears t (family (leaves s) F) v
  · exact Or.inl hclear
  · right
    obtain ⟨A,hA,hAv⟩ : ∃ A ∈ family (leaves s) F, v ∈ minimalVertices A t := by
      simpa only [Clears,Classical.not_forall,Classical.not_imp,Classical.not_not,exists_prop] using hclear
    intro B hB hBv
    have aa := (mem_family _ _ _).1 hA
    have bb := (mem_family _ _ _).1 hB
    have hAB : A ≠ B := by
      intro he
      obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil A (checked_nonempty _ _ hF A aa.1)
      exact source_labels_disjoint t ss hp s r hs hr hne x (aa.2 hx) (bb.2 (he ▸ hx))
    exact pairwise_distinct t F hE A B aa.1 bb.1 hAB v hAv hBv

theorem actual_parent_regions (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (s r : Tree) (hs : s ∈ ss) (hr : r ∈ ss) (hne : s ≠ r) (v : RMAF.Vertex)
    (hv : v ∈ minimalVertices (leaves s) t) (hw : v ∈ minimalVertices (leaves r) t) :
    (¬selectedLeaves (leaves s) t v) ∧ (¬selectedLeaves (leaves r) t v) ∧
    ((regions (leaves s) t v).length = 2 ∨ (regions (leaves s) t v).length = 3) ∧
    ((regions (leaves r) t v).length = 2 ∨ (regions (leaves r) t v).length = 3) := by
  have hn := disjoint_parent_overlap_nonlabel _ _ t v
    (source_labels_disjoint t ss hp s r hs hr hne) hv hw
  exact ⟨hn.1,hn.2,executable_region_count_two_or_three _ t v hn.1 hv,
    executable_region_count_two_or_three _ t v hn.2 hw⟩

theorem core_emission_positive (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (s : Tree) (hs : s ∈ ss) (v : RMAF.Vertex)
    (hn : ¬selectedLeaves (leaves s) t v) (hv : v ∈ minimalVertices (leaves s) t)
    (q : Nat) (o : Output) (ho : o ∈ (generate s (colorLabel t v) q).outputs) :
    1 ≤ o.sourceCuts.length := by
  have hsupp := (proper_source_labels t ss hp s hs).2
  have hr := original_colors_at_least_two (leaves s) t v (proper_parts _ _ hp).1 hsupp hn hv
  have hc := generate_color_cost s (colorLabel t v) q o ho
  change 2 ≤ (dedupNat ((leaves s).map (colorLabel t v))).length at hr
  omega

theorem two_actual_cores_mass (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (s r : Tree) (hs : s ∈ ss) (hr : r ∈ ss) (hne : s ≠ r) (v : RMAF.Vertex)
    (hv : v ∈ minimalVertices (leaves s) t) (hw : v ∈ minimalVertices (leaves r) t)
    (q : Nat) (c : Rat) (hc : 2 ≤ c) :
    rawQMass c ((generate s (colorLabel t v) q).outputs ++
      (generate r (colorLabel t v) q).outputs) ≤ 2 * c ^ (-1 : Int) := by
  have hn := actual_parent_regions t ss hp s r hs hr hne v hv hw
  have hsc := original_colors_at_least_two (leaves s) t v (proper_parts _ _ hp).1
    (proper_source_labels t ss hp s hs).2 hn.1 hv
  have hrc := original_colors_at_least_two (leaves r) t v (proper_parts _ _ hp).1
    (proper_source_labels t ss hp r hr).2 hn.2.1 hw
  have a := generate_mass_of_count s (colorLabel t v) q 1 c hc hsc
  have b := generate_mass_of_count r (colorLabel t v) q 1 c hc hrc
  rw [rawQMass_append]
  grind

theorem member_le_sum (L : List Nat) (n : Nat) (hn : n ∈ L) : n ≤ L.sum := by
  induction L with
  | nil => simp at hn
  | cons a L ih =>
    rcases List.mem_cons.1 hn with rfl | h
    · simp only [List.sum_cons]; omega
    · have := ih h
      simp only [List.sum_cons]; omega

theorem family_cost_le (t : Tree) (ss : List Tree) (F : Forest)
    (ha : agrees (some t) ss F = true) (s : Tree) (hs : s ∈ ss) :
    (family (leaves s) F).length - 1 ≤ additionalCost ss F := by
  have hb := source_blocks_balance _ _ _ ha
  have hl := member_le_sum (ss.map (fun s => (family (leaves s) F).length - 1)) _
    (List.mem_map.2 ⟨s,hs,rfl⟩)
  simp only [additionalCost]
  omega

theorem clearing_component_coverage (t : Tree) (pre : List Tree) (s : Tree) (post : List Tree)
    (F : Forest) (ha : agrees (some t) (pre ++ [s] ++ post) F = true)
    (v : RMAF.Vertex) (hn : ¬selectedLeaves (leaves s) t v)
    (hclear : Clears t (family (leaves s) F) v) (q : Nat)
    (hq : additionalCost (pre ++ [s] ++ post) F ≤ q) :
    ∃ o, o ∈ (generate s (colorLabel t v) q).outputs ∧
      agrees (some t) (replaced pre s post o.partition) F = true ∧
      additionalCost (pre ++ [s] ++ post) F =
        o.sourceCuts.length + additionalCost (replaced pre s post o.partition) F ∧
      o.sourceCuts.length ≤ q ∧
      additionalCost (replaced pre s post o.partition) F ≤ q - o.sourceCuts.length := by
  obtain ⟨hp,hF,hown,hE,hS⟩ := agrees_parts _ _ _ ha
  have hs : s ∈ pre ++ [s] ++ post := by simp
  have sc := hS s hs
  simp only [sourceCheck,Bool.and_eq_true] at sc
  have mono : ∀ B ∈ family (leaves s) F, LabelMonochromatic (colorLabel t v) B := by
    intro B hB
    have bb := (mem_family _ _ _).1 hB
    have hnb : ¬selectedLeaves B t v := by
      intro h
      exact hn (selected_leaves_mono B (leaves s) t bb.2 v h)
    exact (original_label_avoids_iff t B v (proper_parts _ _ hp).1
      (fun _ hx => checked_label _ _ hF bb.1 hx) hnb).1 (hclear B hB)
  have hloc : (family (leaves s) F).length - 1 ≤ q :=
    Nat.le_trans (family_cost_le t _ F ha s hs) hq
  obtain ⟨o,ho,href,hbudget⟩ := generate_partition_coverage_paid s (family (leaves s) F)
    (colorLabel t v) (proper_source_labels t _ hp s hs).1 sc.1.1 sc.2 mono q hloc
  have hQ := (generated_source_valid s (colorLabel t v) q o ho).1
  have hnew := replacement_forward t pre s post o.partition F ha hQ href
  have he := emitted_replacement_cost t pre s post _ q o ho F hnew
  exact ⟨o,ho,hnew,he,hbudget,by omega⟩

end GenericForest
