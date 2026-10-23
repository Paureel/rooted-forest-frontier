import InitialCoverage

namespace Universal233.CutRealization
open RMAF CoreGraph CoreProgram Integration List

theorem group_pure {color t v g} (h : PureGroups color t) (hv : GroupLeafAt t v g) :
    ∀ x, x ∈ g.labels → color x = g.color := by
  induction t generalizing v with
  | leaf a => obtain ⟨rfl,rfl⟩ := (groupLeaf_leaf a g v).1 hv; exact h
  | node p l r ihl ihr =>
    cases v with
    | nil => simp [GroupLeafAt,groupAt] at hv
    | cons s v => cases s <;> first | exact ihl h.1 hv | exact ihr h.2 hv

theorem erase_pure {color t u v g} (e : GLeafErase t u v g) (h : PureGroups color t) : PureGroups color u := by
  induction e with
  | rootLeft => exact h.2
  | rootRight => exact h.1
  | left p r e ih => exact ⟨ih h.1,h.2⟩
  | right p l e ih => exact ⟨h.1,ih h.2⟩

theorem History.pure {T color t d c} (h : History T color t d c) (hn : (leaves T).Nodup) :
    PureGroups color t ∧ ∀ g, g ∈ d → ∀ x, x ∈ g.labels → color x = g.color := by
  induction h with
  | initial => exact ⟨fromTree_pure _ _ _,by intro g hg; cases hg⟩
  | normalized h ih => exact ⟨normalize_pure _ _ ih.1,ih.2⟩
  | @detached t d c next v g h hv hvr hgr hgc he ih =>
    obtain ⟨u,hu,⟨e⟩⟩ := erase_leaf_realization t (h.invariant hn).originNodup v g hv hvr
    have eu : u = next := Option.some.inj (hu.symm.trans he)
    subst u
    refine ⟨erase_pure e ih.1,?_⟩
    intro a ha
    rcases List.mem_cons.1 ha with ea | ha
    · subst a; exact group_pure ih.1 hv
    · exact ih.2 a ha

theorem choose_finish_uniform (t : GTree) (hc : choose t = .finish) :
    ∃ c, ∀ g, g ∈ groups t → g.color = c := by
  cases hgs : groups t with
  | nil => simp [choose,hgs] at hc
  | cons a rest =>
    by_cases hall : (a :: rest).all (fun g => g.color == a.color) = true
    · exact ⟨a.color,by intro g hg; exact beq_iff_eq.1 (List.all_eq_true.1 hall g (hgs ▸ hg))⟩
    · simp only [choose,hgs,hall,ite_false] at hc
      cases hf : (a :: rest).find? (fun g => ((a :: rest).filter (fun h => h.color == g.color)).length == 1) with
      | some g => simp [hf] at hc
      | none =>
        simp only [hf] at hc
        cases hm : mixedCherry t with
        | none => simp [hm] at hc
        | some pair => cases pair with
          | mk x y =>
            by_cases hxy : (x.color == y.color) = true <;> simp [hm,hxy] at hc

theorem finish_monochromatic {T color t d c} (h : History T color t d c)
    (hn : (leaves T).Nodup) (hf : choose t = .finish) :
    ∀ b, b ∈ d.map Group.labels ++ [(groups t).flatMap Group.labels] →
      VertexGeometry.LabelMonochromatic color b := by
  have hp := h.pure hn
  obtain ⟨col,hcol⟩ := choose_finish_uniform t hf
  intro b hb x y hx hy
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨g,hg,rfl⟩ := List.mem_map.1 hb
    exact (hp.2 g hg x hx).trans (hp.2 g hg y hy).symm
  · have he : b = (groups t).flatMap Group.labels := by simpa using hb
    subst b
    obtain ⟨gx,hgx,hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨gy,hgy,hy⟩ := List.mem_flatMap.1 hy
    obtain ⟨vx,hvx⟩ := groupLeaf_of_groups_mem t gx hgx
    obtain ⟨vy,hvy⟩ := groupLeaf_of_groups_mem t gy hgy
    exact (group_pure hp.1 hvx x hx).trans ((hcol gx hgx).trans
      ((hcol gy hgy).symm.trans (group_pure hp.1 hvy y hy).symm))

theorem generate_monochromatic (T : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate T color q).outputs) :
    ∀ b, b ∈ o.partition → VertexGeometry.LabelMonochromatic color b := by
  obtain ⟨hn,t,d,c,hh,hfinish,he⟩ := generate_finish_trace T color q o ho
  subst o
  exact finish_monochromatic hh hn hfinish

theorem realized_covers_labels {T o} (h : RealizedOutput T o) {x : Nat} (hx : x ∈ leaves T) :
    ∃ b, b ∈ o.partition ∧ x ∈ b := by
  obtain ⟨a,ha⟩ := leaf_exists hx
  obtain ⟨hg,hact,comps,hroots,hblocks,hexact,hnd,hcover,hsep,hno,hcost⟩ := h
  obtain ⟨r,hr,hw⟩ := hcover a ha.valid
  obtain ⟨pair,hpair,he⟩ := List.mem_map.1 hr
  have hpairEq : pair = (r,pair.2) := by cases pair; simp_all
  have hh := hexact r pair.2 (hpairEq ▸ hpair)
  exact ⟨pair.2,hblocks ▸ List.mem_map.2 ⟨pair,hpair,rfl⟩,(hh.exact a x ha).2 hw⟩

theorem realized_blocks_nonempty {T o} (h : RealizedOutput T o) (b : List Nat) (hb : b ∈ o.partition) :
    b ≠ [] := by
  obtain ⟨hg,hact,comps,hroots,hblocks,hexact,hnd,hcover,hsep,hno,hcost⟩ := h
  rw [←hblocks] at hb
  obtain ⟨pair,hpair,rfl⟩ := List.mem_map.1 hb
  have hpairEq : pair = (pair.1,pair.2) := by cases pair; rfl
  exact (hexact pair.1 pair.2 (hpairEq ▸ hpair)).nonempty

theorem color_dedup_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons x xs =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.2
    constructor
    · intro hx
      have hm := List.mem_eraseDups.1 hx
      have hn := (List.mem_filter.1 hm).2
      simp at hn
    · exact color_dedup_nodup _
termination_by xs.length
decreasing_by have hh := List.length_filter_le (fun b => !b == x) xs; simp only [List.length_cons]; omega

/-- Number of distinct input colors, defined from executable finite leaf data. -/
def colorCount (T : Tree) (color : Nat → Nat) : Nat := ((leaves T).map color).eraseDups.length

theorem realized_color_lower_bound {T color o} (hr : RealizedOutput T o)
    (hm : ∀ b, b ∈ o.partition → VertexGeometry.LabelMonochromatic color b) :
    colorCount T color ≤ o.sourceCuts.length + 1 := by
  let cols := o.partition.map (fun b => color (b.headD 0))
  have hsub : ((leaves T).map color).eraseDups ⊆ cols := by
    intro c hc
    obtain ⟨x,hx,hxc⟩ := List.mem_map.1 (List.mem_eraseDups.1 hc)
    obtain ⟨b,hb,hxb⟩ := realized_covers_labels hr hx
    have hne := realized_blocks_nonempty hr b hb
    have hh : b.headD 0 ∈ b := by cases b <;> simp_all
    have he : color x = color (b.headD 0) := hm b hb x (b.headD 0) hxb hh
    exact List.mem_map.2 ⟨b,hb,he.symm.trans hxc⟩
  have hlen := (color_dedup_nodup ((leaves T).map color)).length_le_of_subset hsub
  have hs : o.partition.length = o.sourceCuts.length + 1 := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hh⟩ := hr
    exact hh
  simpa only [colorCount,cols,List.length_map,hs] using hlen

theorem generate_realized_color_cost (T : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate T color q).outputs) : colorCount T color - 1 ≤ o.sourceCuts.length := by
  have hh := realized_color_lower_bound (generate_original_realization T color q o ho)
    (generate_monochromatic T color q o ho)
  omega

theorem attempt_cost_bound (f : GTree → List Group → List RMAF.Vertex → Receipt) (q : Nat)
    (hf : ∀ t d c o, o ∈ (f t d c).outputs → o.sourceCuts.length ≤ c.length + q)
    (t d c g o) (ho : o ∈ (attempt f t d c g).outputs) : o.sourceCuts.length ≤ c.length + q + 1 := by
  unfold attempt at ho
  split at ho
  next => simp at ho
  next =>
    split at ho
    next => simp at ho
    next =>
      split at ho
      next => simp at ho
      next u hu =>
        have hh := hf u (g :: d) (g.origin :: c) o ho
        simp only [List.length_cons] at hh
        omega

theorem step_cost_bound (f : GTree → List Group → List RMAF.Vertex → Receipt) (q : Nat)
    (hf : ∀ t d c o, o ∈ (f t d c).outputs → o.sourceCuts.length ≤ c.length + q)
    (t d c o) (ho : o ∈ (step f t d c).outputs) : o.sourceCuts.length ≤ c.length + q + 1 := by
  cases hc : choose (normalize t) with
  | finish =>
    have he : o = ⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels],c⟩ := by simpa [step,hc] using ho
    subst o; simp only; omega
  | one g => exact attempt_cost_bound f q hf _ d c g o (by simpa [step,hc,prefixRoot] using ho)
  | two a b =>
    have hh : o ∈ (attempt f (normalize t) d c a).outputs ∨ o ∈ (attempt f (normalize t) d c b).outputs := by
      simpa [step,hc,prefixRoot,combine] using ho
    rcases hh with ha | hb
    · exact attempt_cost_bound f q hf _ d c a o ha
    · exact attempt_cost_bound f q hf _ d c b o hb
  | refuse why => simp [step,hc] at ho

theorem attempt_pruned_outputs (t d c g) :
    (attempt (fun _ _ _ => (⟨[],[],0,0,1⟩ : Receipt)) t d c g).outputs = [] := by
  unfold attempt
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem run_zero_cost (t d c o) (ho : o ∈ (run 0 t d c).outputs) : o.sourceCuts = c := by
  cases hc : choose (normalize t) with
  | finish =>
    have he : o = ⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels],c⟩ := by simpa [run,step,hc] using ho
    subst o; rfl
  | one g => simp [run,step,hc,prefixRoot,attempt_pruned_outputs] at ho
  | two a b => simp [run,step,hc,prefixRoot,combine,attempt_pruned_outputs] at ho
  | refuse why => simp [run,step,hc] at ho

theorem run_cost_bound (q : Nat) (t d c o) (ho : o ∈ (run q t d c).outputs) :
    o.sourceCuts.length ≤ c.length + q := by
  induction q generalizing t d c o with
  | zero => rw [run_zero_cost t d c o ho]; omega
  | succ q ih => have hh := step_cost_bound (run q) q ih t d c o ho; omega

theorem generate_cost_bound (T : Tree) (color : Nat → Nat) (budget : Nat) (o : Output)
    (ho : o ∈ (generate T color budget).outputs) : o.sourceCuts.length ≤ budget := by
  unfold generate at ho
  split at ho
  next => have hh := run_cost_bound _ _ _ _ o ho; simp only [List.length_nil,Nat.zero_add] at hh; omega
  next => simp at ho

/-- Complete source-core correctness/coverage consumer, without a raw mass or
polynomial-work assertion. The output uses actual nonredundant original cuts. -/
theorem source_core (T : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hn : (leaves T).Nodup) (hp : partitionCheck (leaves T) bs = true)
    (he : pairwiseEmbeddings T bs = true)
    (hm : ∀ b, b ∈ bs → VertexGeometry.LabelMonochromatic color b) :
    ∃ o, o ∈ (generate T color (bs.length - 1)).outputs ∧
      VertexGeometry.Refines bs o.partition ∧ RealizedOutput T o ∧
      (∀ b, b ∈ o.partition → VertexGeometry.LabelMonochromatic color b) ∧
      colorCount T color - 1 ≤ o.sourceCuts.length ∧ o.sourceCuts.length ≤ bs.length - 1 := by
  obtain ⟨o,ho,href,hreal⟩ := generate_refinement_coverage T bs color hn hp he hm _ (Nat.le_refl _)
  exact ⟨o,ho,href,hreal,generate_monochromatic T color _ o ho,
    generate_realized_color_cost T color _ o ho,generate_cost_bound T color _ o ho⟩

end Universal233.CutRealization
