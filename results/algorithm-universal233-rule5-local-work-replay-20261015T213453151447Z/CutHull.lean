import MixedPort
namespace OrdinaryCommonSplit
open RMAF VertexGeometry PairGeometry RestrictionBridge

theorem side_opposite {p : VertexGeometry.Vertex} {b inside : Bool} {v : VertexGeometry.Vertex}
    (h : IsSide p b inside v) (g : IsSide p b (!inside) v) : False := by
  cases inside with
  | false => exact h g
  | true => exact g h

theorem cut_side_convex (p : VertexGeometry.Vertex) (b inside : Bool) :
    Convex (IsSide p b inside) := by
  intro v a z ha hz hp
  cases inside with
  | false =>
    have ea : region (p++[b]) a=2 := (region_up_iff _ _).2 ha
    have ez : region (p++[b]) z=2 := (region_up_iff _ _).2 hz
    have ev := region_path_closed hp (p++[b]) (ea.trans ez.symm)
    exact (region_up_iff _ _).1 (ev.trans ea)
  | true =>
    have ea := (region_child_iff p a b).2 ha
    have ez := (region_child_iff p z b).2 hz
    have ev := region_path_closed hp p (ea.trans ez.symm)
    exact (region_child_iff p v b).1 (ev.trans ea)

theorem cut_side_hull (p : VertexGeometry.Vertex) (b inside : Bool)
    (A : VertexGeometry.Vertex → Prop) (sub : ∀a,A a→IsSide p b inside a)
    (v : VertexGeometry.Vertex) (h : Hull A v) : IsSide p b inside v := by
  obtain ⟨a,z,ha,hz,hp⟩ := h
  exact cut_side_convex p b inside v a z (sub a ha) (sub z hz) hp

theorem region_equal_across_cut (p : VertexGeometry.Vertex) (b inside : Bool)
    (v a z : VertexGeometry.Vertex) (hv : IsSide p b (!inside) v)
    (ha : IsSide p b inside a) (hz : IsSide p b inside z) : region v a=region v z := by
  apply Classical.byContradiction
  intro hn
  exact side_opposite (cut_side_convex p b inside v a z ha hz (region_ne_path v a z hn)) hv

/-- Replace the endpoint beyond the actual cut without changing the part of
the path on the other side. No shared-edge triangle hypothesis is used. -/
theorem path_replace_across_cut (p : VertexGeometry.Vertex) (b inside : Bool)
    (v a z y : VertexGeometry.Vertex) (hv : IsSide p b inside v)
    (hz : IsSide p b (!inside) z) (hy : IsSide p b (!inside) y)
    (hp : PathAt v a z) : PathAt v a y := by
  by_cases hva : v=a
  · subst v;exact .endpointL a y
  · have hvz : v≠z := by intro he;subst z;exact side_opposite hv hz
    have eqr := region_equal_across_cut p b (!inside) v z y (by simpa using hv) hz hy
    exact region_ne_path v a y (by rw [←eqr];exact path_region_ne v a z hp (Ne.symm hva) (Ne.symm hvz))

/-- A mixed component's hull on one side is already contained in the hull
formed with any representative on the opposite side. This is the graph fact
needed to preserve all unmerged blocks during marker-block surgery. -/
theorem cut_hull_replace (p : VertexGeometry.Vertex) (b inside : Bool)
    (A B : VertexGeometry.Vertex → Prop) (y v : VertexGeometry.Vertex)
    (_hA : ∀a,A a→IsSide p b inside a)
    (hB : ∀a,B a→IsSide p b (!inside) a)
    (hy : IsSide p b (!inside) y) (hv : IsSide p b inside v)
    (h : Hull (fun a => A a ∨ B a) v) : Hull (fun a => A a ∨ a=y) v := by
  obtain ⟨a,z,ha,hz,hp⟩ := h
  rcases ha with ha | ha <;> rcases hz with hz | hz
  · exact ⟨a,z,Or.inl ha,Or.inl hz,hp⟩
  · exact ⟨a,y,Or.inl ha,Or.inr rfl,path_replace_across_cut p b inside v a z y hv (hB z hz) hy hp⟩
  · exact ⟨z,y,Or.inl hz,Or.inr rfl,path_replace_across_cut p b inside v z a y hv (hB a ha) hy (path_sym hp)⟩
  · exact False.elim (side_opposite hv (cut_side_convex p b (!inside) v a z (hB a ha) (hB z hz) hp))

theorem selected_append (t : Tree) (K L : List Nat) (v : RMAF.Vertex) :
    selectedLeaves (K++L) t v ↔ selectedLeaves K t v ∨ selectedLeaves L t v := by
  constructor
  · intro h
    obtain ⟨x,hx,ha⟩ := (selected_decompose_label (K++L) t v).1 h
    rcases List.mem_append.1 hx with hx | hx
    · exact Or.inl ((selected_decompose_label K t v).2 ⟨x,hx,ha⟩)
    · exact Or.inr ((selected_decompose_label L t v).2 ⟨x,hx,ha⟩)
  · intro h
    rcases h with h | h
    · obtain ⟨x,hx,ha⟩ := (selected_decompose_label K t v).1 h
      exact (selected_decompose_label (K++L) t v).2 ⟨x,List.mem_append_left _ hx,ha⟩
    · obtain ⟨x,hx,ha⟩ := (selected_decompose_label L t v).1 h
      exact (selected_decompose_label (K++L) t v).2 ⟨x,List.mem_append_right _ hx,ha⟩

theorem singleton_selected_iff (t : Tree) (y : Nat) (a v : RMAF.Vertex)
    (nd : (leaves t).Nodup) (ha : selectedLeaves [y] t a) :
    selectedLeaves [y] t v ↔ v=a := by
  exact ⟨fun hv => singleton_selected_address_unique t y nd v a hv ha,fun he => he ▸ ha⟩

theorem selected_side_of_labels (t : Tree) (K : List Nat) (p : RMAF.Vertex) (b inside : Bool)
    (nd : (leaves t).Nodup)
    (hK : ∀x∈K, if inside then x∈descendants t (p++[b]) else x∉descendants t (p++[b])) :
    ∀ a, selectedLeaves K t a→IsSide p b inside a := by
  intro a ha
  obtain ⟨x,hx,hax⟩ := (selected_decompose_label K t a).1 ha
  have hxl := (singleton_selected_exists t x).1 ⟨a,hax⟩
  have haddr := leafAddress_correct t x nd a hax
  cases inside with
  | false =>
    intro hpre
    exact hK x hx ((descendants_mem t _ x).2 ⟨hxl,by simpa only [haddr] using hpre⟩)
  | true =>
    change Prefix (p++[b]) a
    have hh := ((descendants_mem t _ x).1 (hK x hx)).2
    simpa only [haddr] using hh

theorem original_merge_clear (t : Tree) (K L E : List Nat) (y : Nat)
    (p : RMAF.Vertex) (b inside : Bool) (nd : (leaves t).Nodup) (hyl : y∈leaves t)
    (hK : ∀a,selectedLeaves K t a→IsSide p b inside a)
    (hL : ∀a,selectedLeaves L t a→IsSide p b (!inside) a)
    (hE : ∀a,selectedLeaves E t a→IsSide p b inside a)
    (hy : ∀a,selectedLeaves [y] t a→IsSide p b (!inside) a)
    (hc : Clear (minimalVertices (K++[y]) t) (minimalVertices E t)) :
    Clear (minimalVertices (K++L) t) (minimalVertices E t) := by
  intro v hv hEspan
  obtain ⟨a,ha⟩ := (singleton_selected_exists t y).2 hyl
  have vside := cut_side_hull p b inside (selectedLeaves E t) hE v
    ((minimalVertices_correct E t v).1 hEspan)
  have hm : Hull (fun z => selectedLeaves K t z ∨ selectedLeaves L t z) v :=
    (hull_congr _ _ (selected_append t K L) v).1 ((minimalVertices_correct (K++L) t v).1 hv)
  have hrep := cut_hull_replace p b inside (selectedLeaves K t) (selectedLeaves L t)
    a v hK hL (hy a ha) vside hm
  have hrep' : Hull (selectedLeaves (K++[y]) t) v := by
    apply (hull_congr _ _ (fun z => (selected_append t K [y] z).trans
      (or_congr Iff.rfl (singleton_selected_iff t y a z nd ha))) v).2
    exact hrep
  exact hc v ((minimalVertices_correct (K++[y]) t v).2 hrep') hEspan
end OrdinaryCommonSplit
