import History

/-! Actual full-original-graph component realization for every production output.
No coverage or mass bound is inferred from this soundness theorem. -/
namespace Universal233.CutRealization
open RMAF CoreGraph CoreProgram Integration List

structure ComponentLabels (T : Tree) (cuts : List RMAF.Vertex)
    (r : RMAF.Vertex) (L : List Nat) : Prop where
  actual : Valid T r
  labelsValid : LabelsValid T L
  nonempty : L ≠ []
  exact : ∀ a x, LeafAt T a x → (x ∈ L ↔ ResidualWalk T cuts r a)

theorem component_of_region {T cuts r L} (hc : CutHistory T cuts)
    (hr : r = [] ∨ r ∈ cuts) (hv : LabelsValid T L) (hne : L ≠ [])
    (he : ∀ a x, LeafAt T a x → (x ∈ L ↔ Region cuts r a)) :
    ComponentLabels T cuts r L := by
  refine ⟨hc.root_valid hr,hv,hne,?_⟩
  intro a x ha
  rw [he a x ha,region_component hr (hc.root_valid hr) (region_self cuts r)]
  simp only [ha.valid,true_and]

def pairs (t : GTree) (d : List Group) : List (RMAF.Vertex × List Nat) :=
  d.map (fun g => (g.origin,g.labels)) ++ [([],payload t)]

/-- Component list is in literal output order: detached components followed by
the live original-root component. Full components include all original vertices. -/
def RealizedOutput (T : Tree) (o : Output) : Prop :=
  GoodCuts o.sourceCuts ∧
  (∀ p, p ∈ o.sourceCuts → Valid T p) ∧
  ∃ components : List (RMAF.Vertex × List Nat),
    components.map Prod.fst = o.sourceCuts ++ [[]] ∧
    components.map Prod.snd = o.partition ∧
    (∀ r L, (r,L) ∈ components → ComponentLabels T o.sourceCuts r L) ∧
    (components.map Prod.fst).Nodup ∧
    (∀ v, Valid T v → ∃ r, r ∈ components.map Prod.fst ∧ ResidualWalk T o.sourceCuts r v) ∧
    (∀ r, r ∈ components.map Prod.fst → ∀ s, s ∈ components.map Prod.fst →
      (ResidualWalk T o.sourceCuts r s ↔ r = s)) ∧
    (∀ v, Valid T v → ∃ a x, LeafAt T a x ∧ ResidualWalk T o.sourceCuts v a) ∧
    o.partition.length = o.sourceCuts.length + 1

theorem roots_nodup {c : List RMAF.Vertex} (hc : GoodCuts c) : (c ++ [[]]).Nodup := by
  apply List.nodup_append.2
  refine ⟨hc.1,by simp,?_⟩
  intro a ha b hb he
  have hb0 : b = [] := by simpa using hb
  exact hc.2 a ha (he.trans hb0)

theorem History.pair_components {T color t d c} (h : History T color t d c)
    (hn : (leaves T).Nodup) :
    ∀ r L, (r,L) ∈ pairs t d → ComponentLabels T c r L := by
  have hi := h.invariant hn
  intro r L hp
  simp only [pairs,List.mem_append,List.mem_map,List.mem_singleton,Prod.mk.injEq] at hp
  rcases hp with ⟨g,hg,hgr,hgl⟩ | ⟨hr,hL⟩
  · subst r; subst L
    have hc : g.origin ∈ c := by rw [←hi.cutMap]; exact List.mem_map.2 ⟨g,hg,rfl⟩
    have hh := hi.detached g hg
    exact component_of_region hi.cutHistory (Or.inr hc) hh.labelsValid hh.nonempty hh.exact
  · subst r; subst L
    have hf := hi.display.facts
    apply component_of_region hi.cutHistory (Or.inl rfl) hf.labelsValid hf.nonempty
    intro a x ha
    rw [hf.exactBase a x ha,region_root c a hi.cutHistory.good.2]
    simp

theorem History.finish_realizes {T color t d c} (h : History T color t d c)
    (hn : (leaves T).Nodup) :
    RealizedOutput T ⟨d.map Group.labels ++ [(groups t).flatMap Group.labels],c⟩ := by
  have hi := h.invariant hn
  have hf := hi.display.facts
  have roots : (pairs t d).map Prod.fst = c ++ [[]] := by
    simpa [pairs,List.map_map,Function.comp_def] using congrArg (· ++ [[]]) hi.cutMap
  have blocks : (pairs t d).map Prod.snd = d.map Group.labels ++ [(groups t).flatMap Group.labels] := by
    simp [pairs,List.map_map,payload_groups]
  have hcomponents := h.pair_components hn
  refine ⟨hi.cutHistory.good,hi.cutHistory.actual,pairs t d,roots,blocks,hcomponents,
    roots ▸ roots_nodup hi.cutHistory.good,?_,?_,?_,?_⟩
  · intro v hv
    obtain ⟨r,hr,hw⟩ := hi.cutHistory.all_components v hv
    refine ⟨r,?_,hw⟩
    rw [roots]
    simpa [or_comm] using hr
  · intro r hr s hs
    rw [roots] at hr hs
    have hrr : r = [] ∨ r ∈ c := by simpa [or_comm] using hr
    have hss : s = [] ∨ s ∈ c := by simpa [or_comm] using hs
    exact hi.cutHistory.rooted_components hrr hss
  · intro v hv
    obtain ⟨r,hr,hw⟩ := hi.cutHistory.all_components v hv
    have hrmem : r ∈ (pairs t d).map Prod.fst := by rw [roots]; simpa [or_comm] using hr
    obtain ⟨pair,hpair,he⟩ := List.mem_map.1 hrmem
    have hepair : pair = (r,pair.2) := by cases pair; simp_all
    have hc := hcomponents r pair.2 (hepair ▸ hpair)
    cases hL : pair.2 with
    | nil => exact False.elim (hc.nonempty hL)
    | cons x xs =>
      have hx : x ∈ pair.2 := by rw [hL]; simp
      obtain ⟨a,ha⟩ := hc.labelsValid x hx
      exact ⟨a,x,ha,hw.reverse.trans ((hc.exact a x ha).1 hx)⟩
  · have hlen := congrArg List.length hi.cutMap
    simp only [List.length_map] at hlen
    simp [hlen]

/-- Every literal production output is exactly the leaf partition of all
components produced by its nonredundant ORIGINAL cuts. All components contain
an original leaf, including those containing suppressed original vertices. -/
theorem generate_original_realization (T : Tree) (color : Nat → Nat) (q : Nat)
    (o : Output) (ho : o ∈ (generate T color q).outputs) : RealizedOutput T o := by
  obtain ⟨hn,t,d,c,hh,hfinish,he⟩ := generate_finish_trace T color q o ho
  subst o
  exact hh.finish_realizes hn

/-- Explicit graph version of the continuation's two leaf-bearing components. -/
theorem History.continuation_components {T color t d c next v g}
    (h : History T color t d c) (hn : (leaves T).Nodup)
    (hv : GroupLeafAt t v g) (hvr : v ≠ []) (hgr : g.origin ≠ [])
    (hgc : g.origin ∉ c) (he : erase g.origin t = some next) :
    ComponentLabels T (g.origin :: c) g.origin g.labels ∧
    ComponentLabels T (g.origin :: c) [] (payload next) ∧
    (∀ r, r ∈ c → ∀ a, ResidualWalk T (g.origin :: c) r a ↔ ResidualWalk T c r a) ∧
    ¬ ResidualWalk T (g.origin :: c) [] g.origin := by
  have hs := h.selected hn hv
  have hh : History T color next (g :: d) (g.origin :: c) := .detached h hv hvr hgr hgc he
  have hi := hh.invariant hn
  have old := h.invariant hn
  have hc := hi.cutHistory
  have gf := hi.detached g (by simp)
  refine ⟨component_of_region hc (Or.inr (by simp)) gf.labelsValid gf.nonempty gf.exact,?_,?_,?_⟩
  · have hf := hi.display.facts
    apply component_of_region hc (Or.inl rfl) hf.labelsValid hf.nonempty
    intro a x ha
    rw [hf.exactBase a x ha,region_root _ a hc.good.2]
    simp
  · intro r hr a
    rw [region_component (Or.inr (List.mem_cons_of_mem g.origin hr)) (old.cutHistory.actual r hr) (region_self _ r),
      region_component (Or.inr hr) (old.cutHistory.actual r hr) (region_self _ r),
      prior_region_unchanged hs.2.1 hr]
  · intro hw
    have heq := (hc.rooted_components (Or.inl rfl) (Or.inr (by simp))).1 hw
    exact hgr heq.symm

end Universal233.CutRealization
