import Regions

/-! Exact-operation reachability. Constructors accept only executable operation
facts and guard/selection facts. No original residual correspondence is an input.
The invariant and emitted-output realization are derived below. -/
namespace Universal233.CutRealization
open RMAF CoreGraph CoreProgram Integration List

inductive History (T : Tree) (color : Nat → Nat) :
    GTree → List Group → List RMAF.Vertex → Prop
  | initial : History T color (fromTree color [] T) [] []
  | normalized {t d c} : History T color t d c → History T color (normalize t) d c
  | detached {t d c next v g} : History T color t d c → GroupLeafAt t v g →
      v ≠ [] → g.origin ≠ [] → g.origin ∉ c → erase g.origin t = some next →
      History T color next (g :: d) (g.origin :: c)

structure DetachedFacts (T : Tree) (cuts : List RMAF.Vertex) (g : Group) : Prop where
  labelsValid : LabelsValid T g.labels
  nonempty : g.labels ≠ []
  exact : ∀ a x, LeafAt T a x → (x ∈ g.labels ↔ Region cuts g.origin a)

structure StateInvariant (T : Tree) (color : Nat → Nat)
    (t : GTree) (d : List Group) (c : List RMAF.Vertex) : Prop where
  display : Models T c [] t
  payloadNodup : (payload t).Nodup
  originSublist : origins t <+ origins (fromTree color [] T)
  cutHistory : CutHistory T c
  cutMap : d.map Group.origin = c
  detached : ∀ g, g ∈ d → DetachedFacts T c g

theorem StateInvariant.originNodup {T color t d c} (h : StateInvariant T color t d c) :
    (origins t).Nodup := h.originSublist.nodup (fromTree_origins_nodup color [] T)

theorem History.invariant {T color t d c} (h : History T color t d c)
    (hn : (leaves T).Nodup) : StateInvariant T color t d c := by
  induction h with
  | initial =>
    refine ⟨fromTree_models color hn rfl,?_,.refl _,.nil,rfl,?_⟩
    · simpa only [fromTree_payload] using hn
    · intro g hg; cases hg
  | normalized h ih =>
    exact ⟨normalize_models ih.display,by simpa only [normalize_payload] using ih.payloadNodup,
      (normalize_origins_sublist _).trans ih.originSublist,ih.cutHistory,ih.cutMap,ih.detached⟩
  | @detached t d c next v g h hv hvr hgr hgc he ih =>
    obtain ⟨base,hgm⟩ := group_model ih.display hv
    have gf := hgm.facts
    have hg : Exact T c g.origin g.labels := gf.exactRoot
    obtain ⟨u,hu,⟨e⟩⟩ := erase_leaf_realization t ih.originNodup v g hv hvr
    have eu : u = next := Option.some.inj (hu.symm.trans he)
    subst u
    have hp := gleaf_payload_perm e
    have hnd := List.nodup_append.1 (hp.nodup ih.payloadNodup)
    refine ⟨gleaf_models e ih.display ih.payloadNodup hg,hnd.2.1,
      (erase_origins_sublist t g.origin next he).trans ih.originSublist,
      .cons g.origin ih.cutHistory gf.actual hgr gf.live,?_,?_⟩
    · simpa using congrArg (g.origin :: ·) ih.cutMap
    · intro a ha
      rcases List.mem_cons.1 ha with hea | ha
      · subst a
        exact ⟨gf.labelsValid,gf.nonempty,fun w x hw => (hg w x hw).trans (new_region gf.live).symm⟩
      · have old := ih.detached a ha
        have hac : a.origin ∈ c := by rw [←ih.cutMap]; exact List.mem_map.2 ⟨a,ha,rfl⟩
        exact ⟨old.labelsValid,old.nonempty,fun w x hw =>
          (old.exact w x hw).trans (prior_region_unchanged gf.live hac).symm⟩

/-- Derived selected-origin semantics on every exact-operation reachable state. -/
theorem History.selected {T color t d c} (h : History T color t d c)
    (hn : (leaves T).Nodup) {v : RMAF.Vertex} {g : Group} (hv : GroupLeafAt t v g) :
    Valid T g.origin ∧ Live c g.origin ∧ g.labels ≠ [] ∧
      LabelsValid T g.labels ∧ Exact T c g.origin g.labels := by
  obtain ⟨b,hb⟩ := group_model (h.invariant hn).display hv
  exact ⟨hb.facts.actual,hb.facts.live,hb.facts.nonempty,hb.facts.labelsValid,hb.facts.exactRoot⟩

/-- At the exact successful attempt continuation, the original edge is live,
the new component has exactly the selected payload, and every prior detached
component is unchanged. The next payload is exactly the new live leaf set. -/
theorem History.continuation_realizes {T color t d c next v g}
    (h : History T color t d c) (hn : (leaves T).Nodup)
    (hv : GroupLeafAt t v g) (hvr : v ≠ []) (hgr : g.origin ≠ [])
    (hgc : g.origin ∉ c) (he : erase g.origin t = some next) :
    ResidualAdj T c g.origin.dropLast g.origin ∧
    Live c g.origin.dropLast ∧ Live c g.origin ∧
    (∀ a x, LeafAt T a x → (x ∈ g.labels ↔ Region (g.origin :: c) g.origin a)) ∧
    Exact T (g.origin :: c) [] (payload next) ∧
    g.labels ≠ [] ∧ payload next ≠ [] ∧
    (∀ r, r ∈ c → ∀ a, Region (g.origin :: c) r a ↔ Region c r a) ∧
    (∀ a, Live c a ↔ Live (g.origin :: c) a ∨ Region (g.origin :: c) g.origin a) := by
  have hs := h.selected hn hv
  have hh : History T color next (g :: d) (g.origin :: c) :=
    .detached h hv hvr hgr hgc he
  have hi := hh.invariant hn
  have hedge := live_original_edge hs.1 hgr hs.2.1
  refine ⟨hedge.1,hedge.2.1,hedge.2.2,?_,hi.display.facts.exactBase,
    hs.2.2.1,hi.display.facts.nonempty,?_,?_⟩
  · exact (hi.detached g (by simp)).exact
  · intro r hr a; exact prior_region_unchanged hs.2.1 hr
  · intro a; exact live_component_split hs.2.1

def FinishOf (T : Tree) (color : Nat → Nat) (o : Output) : Prop :=
  ∃ t d c, History T color t d c ∧ choose t = .finish ∧
    o = ⟨d.map Group.labels ++ [(groups t).flatMap Group.labels],c⟩

theorem attempt_finish_trace (T : Tree) (color : Nat → Nat)
    (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (hf : ∀ t d c, History T color t d c → ∀ o, o ∈ (f t d c).outputs → FinishOf T color o)
    (t : GTree) (d : List Group) (c : List RMAF.Vertex) (h : History T color t d c)
    (v : RMAF.Vertex) (g : Group) (hv : GroupLeafAt t v g) (hvr : v ≠ [])
    (o : Output) (ho : o ∈ (attempt f t d c g).outputs) : FinishOf T color o := by
  unfold attempt at ho
  split at ho
  next => simp at ho
  next hgr =>
    split at ho
    next => simp at ho
    next hgc =>
      split at ho
      next => simp at ho
      next next he =>
        apply hf next (g :: d) (g.origin :: c) (.detached h hv hvr hgr ?_ he) o ho
        intro hm; exact hgc (List.contains_iff_mem.2 hm)

theorem step_finish_trace (T : Tree) (color : Nat → Nat)
    (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (hf : ∀ t d c, History T color t d c → ∀ o, o ∈ (f t d c).outputs → FinishOf T color o)
    (t : GTree) (d : List Group) (c : List RMAF.Vertex) (h : History T color t d c)
    (o : Output) (ho : o ∈ (step f t d c).outputs) : FinishOf T color o := by
  have hh := History.normalized h
  cases hc : choose (normalize t) with
  | finish =>
    have he : o = ⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels],c⟩ := by
      simpa [step,hc] using ho
    exact ⟨normalize t,d,c,hh,hc,he⟩
  | one g =>
    obtain ⟨v,hv⟩ := groupLeaf_of_groups_mem _ g (choose_one_selected _ g hc).1
    apply attempt_finish_trace T color f hf _ d c hh v g hv (choose_one_nonroot _ g hc v hv) o
    simpa [step,hc,prefixRoot] using ho
  | two a b =>
    obtain ⟨p,hp,hcol⟩ := choose_two_selected _ a b hc
    have hor : o ∈ (attempt f (normalize t) d c a).outputs ∨
        o ∈ (attempt f (normalize t) d c b).outputs := by
      simpa [step,hc,prefixRoot,combine] using ho
    rcases hor with ha | hb
    · exact attempt_finish_trace T color f hf _ d c hh (p ++ [false]) a
        (gcherry_left hp) (by simp) o ha
    · exact attempt_finish_trace T color f hf _ d c hh (p ++ [true]) b
        (gcherry_right hp) (by simp) o hb
  | refuse why => simp [step,hc] at ho

theorem run_finish_trace {T color t d c} (h : History T color t d c)
    (q : Nat) (o : Output) (ho : o ∈ (run q t d c).outputs) : FinishOf T color o := by
  induction q generalizing t d c o with
  | zero => exact step_finish_trace T color _ (by intros; contradiction) t d c h o ho
  | succ q ih =>
    exact step_finish_trace T color (run q)
      (by intro a b c hh x hx; exact ih hh x hx) t d c h o ho

theorem generate_finish_trace (T : Tree) (color : Nat → Nat) (q : Nat)
    (o : Output) (ho : o ∈ (generate T color q).outputs) :
    (leaves T).Nodup ∧ FinishOf T color o := by
  unfold generate at ho
  split at ho
  next hn => exact ⟨hn,run_finish_trace History.initial _ o ho⟩
  next => simp at ho

end Universal233.CutRealization
