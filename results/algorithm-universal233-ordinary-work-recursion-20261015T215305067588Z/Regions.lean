import Display

namespace Universal233.CutRealization
open RMAF CoreGraph CoreProgram Integration

theorem region_self (cuts : List RMAF.Vertex) (r : RMAF.Vertex) : Region cuts r r :=
  ⟨List.prefix_rfl,fun _ _ h => h⟩

theorem new_region {cuts : List RMAF.Vertex} {q v : RMAF.Vertex} (hq : Live cuts q) :
    Region (q :: cuts) q v ↔ Pre q v ∧ Live cuts v := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    intro p hp hpp
    exact hq p hp (h.2 p (List.mem_cons_of_mem q hp) hpp)
  · rintro ⟨hv,hl⟩
    refine ⟨hv,?_⟩
    intro p hp hpp
    rcases List.mem_cons.1 hp with he | hp
    · subst p; exact List.prefix_rfl
    · exact False.elim (hl p hp hpp)

theorem prior_region_unchanged {cuts : List RMAF.Vertex} {q r v : RMAF.Vertex}
    (hq : Live cuts q) (hr : r ∈ cuts) :
    Region (q :: cuts) r v ↔ Region cuts r v := by
  constructor
  · intro h
    exact ⟨h.1,fun p hp hpp => h.2 p (List.mem_cons_of_mem q hp) hpp⟩
  · intro h
    refine ⟨h.1,?_⟩
    intro p hp hpv
    rcases List.mem_cons.1 hp with he | hp
    · subst p
      rcases List.prefix_or_prefix_of_prefix hpv h.1 with hh | hh
      · exact hh
      · exact False.elim (hq r hr hh)
    · exact h.2 p hp hpv

theorem live_component_split {cuts : List RMAF.Vertex} {q v : RMAF.Vertex}
    (hq : Live cuts q) :
    Live cuts v ↔ Live (q :: cuts) v ∨ Region (q :: cuts) q v := by
  rw [live_cons,new_region hq]
  by_cases hp : Pre q v <;> simp [hp]

theorem new_live_separated {cuts : List RMAF.Vertex} {q v : RMAF.Vertex}
    (hl : Live (q :: cuts) v) (hr : Region (q :: cuts) q v) : False :=
  (live_cons q v cuts).1 hl |>.1 hr.1

inductive CutHistory (T : Tree) : List RMAF.Vertex → Prop
  | nil : CutHistory T []
  | cons {cuts} (q : RMAF.Vertex) : CutHistory T cuts → Valid T q → q ≠ [] →
      Live cuts q → CutHistory T (q :: cuts)

theorem CutHistory.good {T cuts} (h : CutHistory T cuts) : GoodCuts cuts := by
  induction h with
  | nil => exact goodCuts_nil
  | @cons cuts q h hv hn hl ih =>
    apply goodCuts_cons ih hn
    intro hc
    exact hl q (List.contains_iff_mem.1 hc) List.prefix_rfl

theorem CutHistory.actual {T cuts} (h : CutHistory T cuts) :
    ∀ r, r ∈ cuts → Valid T r := by
  induction h with
  | nil => simp
  | @cons cuts q h hv hn hl ih =>
    intro r hr
    rcases List.mem_cons.1 hr with he | hr
    · simpa only [he] using hv
    · exact ih r hr

/-- Every ORIGINAL vertex, including suppressed vertices, has one rooted region. -/
theorem CutHistory.covers {T cuts} (h : CutHistory T cuts) (v : RMAF.Vertex) :
    ∃ r, (r = [] ∨ r ∈ cuts) ∧ Region cuts r v := by
  induction h with
  | nil => exact ⟨[],Or.inl rfl,List.nil_prefix,by simp⟩
  | @cons cuts q h hv hn hl ih =>
    obtain ⟨r,hr,hreg⟩ := ih
    rcases hr with he | hr
    · subst r
      have hlv := (region_root cuts v h.good.2).1 hreg
      rcases (live_component_split hl).1 hlv with hh | hh
      · exact ⟨[],Or.inl rfl,(region_root (q :: cuts) v (CutHistory.cons q h hv hn hl).good.2).2 hh⟩
      · exact ⟨q,Or.inr (by simp),hh⟩
    · exact ⟨r,Or.inr (List.mem_cons_of_mem q hr),(prior_region_unchanged hl hr).2 hreg⟩

theorem CutHistory.root_valid {T cuts} (h : CutHistory T cuts) {r : RMAF.Vertex}
    (hr : r = [] ∨ r ∈ cuts) : Valid T r := by
  rcases hr with he | hr
  · subst r; exact valid_root T
  · exact h.actual r hr

theorem CutHistory.rooted_components {T cuts} (h : CutHistory T cuts)
    {r s : RMAF.Vertex} (hr : r = [] ∨ r ∈ cuts) (hs : s = [] ∨ s ∈ cuts) :
    ResidualWalk T cuts r s ↔ r = s := by
  rw [region_component hr (h.root_valid hr) (region_self cuts r)]
  constructor
  · rintro ⟨hv,hreg⟩
    exact rooted_regions_disjoint hr hs hreg (region_self cuts s)
  · intro he; subst s; exact ⟨h.root_valid hr,region_self cuts r⟩

theorem CutHistory.all_components {T cuts} (h : CutHistory T cuts)
    (v : RMAF.Vertex) (hv : Valid T v) :
    ∃ r, (r = [] ∨ r ∈ cuts) ∧ ResidualWalk T cuts r v := by
  obtain ⟨r,hr,hreg⟩ := h.covers v
  exact ⟨r,hr,region_walk hv hreg⟩

/-- The literal edge into a live nonroot origin is a still-present ORIGINAL
edge of the live original component, even when displayed paths were suppressed. -/
theorem live_original_edge {T cuts q} (hq : Valid T q) (hn : q ≠ []) (hl : Live cuts q) :
    ResidualAdj T cuts q.dropLast q ∧ Live cuts q.dropLast ∧ Live cuts q := by
  rcases List.eq_nil_or_concat q with he | ⟨p,b,he⟩
  · exact False.elim (hn he)
  · have heq : q = p ++ [b] := by simpa only [List.concat_eq_append] using he
    rw [heq] at hq hl ⊢
    have hparent : Pre p (p ++ [b]) := List.prefix_append p [b]
    have hpLive := live_ancestor hl hparent
    have hreg : Region cuts p (p ++ [b]) := ⟨hparent,fun c hc hcp => False.elim (hl c hc hcp)⟩
    exact ⟨by simpa using region_down_edge hreg List.prefix_rfl hq b rfl,by simpa using hpLive,hl⟩

end Universal233.CutRealization
