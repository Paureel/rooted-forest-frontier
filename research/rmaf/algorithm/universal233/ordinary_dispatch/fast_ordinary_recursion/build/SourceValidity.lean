import ChainAssembly

namespace Universal233.Assembly
open RMAF CoreProgram CoreGraph SourceCoverage VertexGeometry

/-- The actual original residual component induces a connected support in the
full original one-edge graph; no suppression display edge is substituted. -/
theorem residual_core_walk {T cuts r a b}
    (w : CutRealization.ResidualWalk T cuts a b)
    (ha : CutRealization.ResidualWalk T cuts r a) :
    CoreGraph.Walk T (CutRealization.ResidualWalk T cuts r) a b := by
  induction w with
  | refl => exact .refl ha
  | @step a b c he tail ih =>
    apply CoreGraph.Walk.step ha he.1
    exact ih (ha.trans (.step he (.refl he.1.2.1)))

theorem residual_component_convex (T : Tree) (cuts : List RMAF.Vertex) (r : RMAF.Vertex) :
    Convex (CutRealization.ResidualWalk T cuts r) := by
  intro v a b ha hb hp
  apply Classical.byContradiction
  intro hn
  have hna : a ≠ v := by intro he; subst a; exact hn ha
  have hnb : b ≠ v := by intro he; subst b; exact hn hb
  have walk := residual_core_walk (ha.reverse.trans hb) ha
  exact path_region_ne v a b hp hna hnb (Integration.walk_avoids_region walk hn)

theorem selected_original_leaf (T : Tree) (L : List Nat) (a : RMAF.Vertex) :
    selectedLeaves L T a ↔ ∃ x, x ∈ L ∧ LeafAt T a x := by
  induction T generalizing a with
  | leaf x =>
    cases a with
    | nil => simp [selectedLeaves,LeafAt,subtree]
    | cons s a => simp [selectedLeaves,LeafAt,subtree]
  | node l r ihl ihr =>
    cases a with
    | nil => simp [selectedLeaves,Join,LeafAt,subtree]
    | cons s a =>
      cases s with
      | false => simpa [selectedLeaves,Join,LeafAt,subtree] using ihl a
      | true => simpa [selectedLeaves,Join,LeafAt,subtree] using ihr a

theorem component_contains_minimal {T cuts r L}
    (h : CutRealization.ComponentLabels T cuts r L) (v : RMAF.Vertex)
    (hv : v ∈ minimalVertices L T) : CutRealization.ResidualWalk T cuts r v := by
  obtain ⟨a,b,ha,hb,hpath⟩ := (minimalVertices_correct L T v).1 hv
  obtain ⟨x,hx,hxa⟩ := (selected_original_leaf T L a).1 ha
  obtain ⟨y,hy,hyb⟩ := (selected_original_leaf T L b).1 hb
  exact residual_component_convex T cuts r v a b ((h.exact a x hxa).1 hx)
    ((h.exact b y hyb).1 hy) hpath

theorem components_pairwise_embeddings (T : Tree) (cuts : List RMAF.Vertex)
    (cs : List (RMAF.Vertex × List Nat))
    (hc : ∀ r L, (r,L) ∈ cs → CutRealization.ComponentLabels T cuts r L)
    (hn : (cs.map Prod.fst).Nodup)
    (hsep : ∀ r, r ∈ cs.map Prod.fst → ∀ s, s ∈ cs.map Prod.fst →
      CutRealization.ResidualWalk T cuts r s → r = s) :
    pairwiseEmbeddings T (cs.map Prod.snd) = true := by
  induction cs with
  | nil => rfl
  | cons p tail ih =>
    rcases p with ⟨r,L⟩
    have hn' := List.nodup_cons.1 hn
    simp only [List.map_cons,pairwiseEmbeddings,Bool.and_eq_true]
    constructor
    · apply List.all_eq_true.2
      intro K hK
      obtain ⟨p,hp,rfl⟩ := List.mem_map.1 hK
      rcases p with ⟨s,M⟩
      apply List.all_eq_true.2
      intro v hv
      simp only [Bool.not_eq_true',Bool.eq_false_iff,ne_eq,List.contains_iff_mem]
      intro hw
      have hr := component_contains_minimal (hc r L (by simp)) v hv
      have hs := component_contains_minimal (hc s M (by simp [hp])) v hw
      have hrs : r = s := hsep r (by simp) s (by exact List.mem_cons_of_mem r (List.mem_map.mpr ⟨(s,M),hp,rfl⟩)) (hr.trans hs.reverse)
      apply hn'.1
      exact List.mem_map.2 ⟨(s,M),hp,hrs.symm⟩
    · apply ih
      · intro s M hp; exact hc s M (by simp [hp])
      · exact hn'.2
      · intro a ha b hb hab
        exact hsep a (by simp [ha]) b (by simp [hb]) hab

/-- A generated partition is source-valid in the ORIGINAL executable checker,
not merely a collection of disjoint displayed pieces. -/
theorem generated_source_valid (T : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate T color q).outputs) :
    partitionCheck (leaves T) o.partition = true ∧ pairwiseEmbeddings T o.partition = true := by
  have hreal := CutRealization.generate_original_realization T color q o ho
  refine ⟨CutRealization.generate_partition_check T color q o ho,?_⟩
  obtain ⟨hg,hact,cs,hroots,hblocks,hc,hn,hcover,hsep,hno,hcost⟩ := hreal
  rw [←hblocks]
  exact components_pairwise_embeddings T o.sourceCuts cs hc hn (fun r hr s hs hw => (hsep r hr s hs).1 hw)

end Universal233.Assembly
