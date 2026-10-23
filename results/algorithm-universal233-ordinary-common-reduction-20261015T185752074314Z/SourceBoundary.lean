import SourceControls
namespace OrdinaryCommonSplit.Source
open RMAF Universal233 CoreGraph Integration VertexGeometry CutRealization HardParent

theorem incident_spec (T : Tree) (X : List Nat) (q : RMAF.Vertex) :
 q ∈ incident T X ↔ Valid T q ∧ q ≠ [] ∧ paint T X q ≠ paint T X q.dropLast := by
 simp [incident,paint,DepthOne.mem_vertices,and_assoc]

/-- An uncut actual original edge preserves the literal hull color if q is
the only incident edge. This is graph connectivity, with no split premise. -/
theorem one_boundary_adj {T : Tree} {X : List Nat} {q u v : RMAF.Vertex}
 (hi : incident T X = [q]) (he : ResidualAdj T [q] u v) :
 paint T X u = paint T X v := by
 have forward {u v : RMAF.Vertex} (he : ResidualAdj T [q] u v)
     (hchild : ∃ s, v = u ++ [s]) : paint T X u = paint T X v := by
   obtain ⟨s,rfl⟩ := hchild
   apply Classical.byContradiction
   intro hn
   have hmem : u ++ [s] ∈ incident T X :=
     (incident_spec T X _).2 ⟨he.1.2.1,by simp,by simpa using Ne.symm hn⟩
   have eq : u ++ [s] = q := by simpa [hi] using hmem
   exact (he.2 q (by simp)).1 ⟨by simpa [←eq],eq⟩
 rcases he.1.2.2 with hs | hs
 · exact forward he hs
 · exact (forward he.symm hs).symm

theorem one_boundary_walk {T : Tree} {X : List Nat} {q u v : RMAF.Vertex}
 (hi : incident T X = [q]) (hw : ResidualWalk T [q] u v) :
 paint T X u = paint T X v := by
 induction hw with
 | refl => rfl
 | step he tail ih => exact (one_boundary_adj hi he).trans ih

theorem one_boundary_regions {T : Tree} {X : List Nat} {q v : RMAF.Vertex}
 (hi : incident T X = [q]) (hv : Valid T v) :
 paint T X v = if q <+: v then paint T X q else paint T X [] := by
 have qm : q ∈ incident T X := by simp [hi]
 have qs := (incident_spec T X q).1 qm
 by_cases hp : q <+: v
 · rw [if_pos hp]
   have seed : Region [q] q q := ⟨List.prefix_rfl,by
     intro p h _; have e : p = q := by simpa using h
     subst p; exact List.prefix_rfl⟩
   have reg : Region [q] q v := ⟨hp,by
     intro p h _; have e : p = q := by simpa using h
     subst p; exact List.prefix_rfl⟩
   have hw := (region_component (Or.inr (by simp)) qs.1 seed).2 ⟨hv,reg⟩
   exact (one_boundary_walk hi hw).symm
 · rw [if_neg hp]
   have seed : Region [q] [] [] := ⟨List.nil_prefix,fun _ _ h => h⟩
   have reg : Region [q] [] v := ⟨List.nil_prefix,by
     intro p h hpre; have e : p = q := by simpa using h
     subst p; exact False.elim (hp hpre)⟩
   have hw := (region_component (Or.inl rfl) (valid_root T) seed).2 ⟨hv,reg⟩
   exact (one_boundary_walk hi hw).symm

theorem one_boundary_colors {T : Tree} {X : List Nat} {q : RMAF.Vertex}
 (hi : incident T X = [q]) : paint T X q ≠ paint T X [] := by
 have qm : q ∈ incident T X := by simp [hi]
 have qs := (incident_spec T X q).1 qm
 have hpvalid : Valid T q.dropLast := valid_ancestor qs.1 (List.dropLast_prefix q)
 have notpre : ¬q <+: q.dropLast := by
   intro hp
   have hh := hp.length_le
   cases q with
   | nil => exact qs.2.1 rfl
   | cons s q => simp at hh; omega
 have color := one_boundary_regions hi hpvalid
 rw [if_neg notpre] at color
 exact fun h => qs.2.2 (h.trans color.symm)

theorem label_prefix {T : Tree} (hn : (leaves T).Nodup)
 {v q : RMAF.Vertex} {x : Nat} (hl : LeafAt T v x) :
 x ∈ DepthOne.subtreeLabels T q ↔ q <+: v := by
 rw [DepthOne.subtreeLabels_mem]
 constructor
 · rintro ⟨w,hw,hp⟩
   have e := leaf_unique hn hw hl
   simpa [e] using hp
 · exact fun hp => ⟨v,hl,hp⟩

/-- Uniform original graph classification for the one-incident-arc boundary.
The X side may be the descendant or root side, covering both source root
orientations. The witness arc is not a suppressed display edge. -/
theorem actual_one_incident_split {T : Tree} {X : List Nat} {q : RMAF.Vertex}
 (hn : (leaves T).Nodup) (hi : incident T X = [q]) :
 Valid T q ∧ q ≠ [] ∧
 ((∀ x, x ∈ leaves T → (x ∈ X ↔ x ∈ DepthOne.subtreeLabels T q)) ∨
  (∀ x, x ∈ leaves T → (x ∈ X ↔ x ∉ DepthOne.subtreeLabels T q))) := by
 have qm : q ∈ incident T X := by simp [hi]
 have qs := (incident_spec T X q).1 qm
 refine ⟨qs.1,qs.2.1,?_⟩
 have diff := one_boundary_colors hi
 have terminal {v : RMAF.Vertex} {x : Nat} (hl : LeafAt T v x) :
     paint T X v = true ↔ x ∈ X := by
   simpa [paint] using minimalVertices_terminal X T v x hl
 cases hq : paint T X q <;> cases hr : paint T X []
 · exact False.elim (diff (hq.trans hr.symm))
 · right
   intro x hx
   obtain ⟨v,hl⟩ := leaf_exists hx
   have side := one_boundary_regions hi hl.valid
   rw [←terminal hl,label_prefix hn hl]
   rw [side,hq,hr]
   by_cases hp : q <+: v <;> simp [hp]
 · left
   intro x hx
   obtain ⟨v,hl⟩ := leaf_exists hx
   have side := one_boundary_regions hi hl.valid
   rw [←terminal hl,label_prefix hn hl]
   rw [side,hq,hr]
   by_cases hp : q <+: v <;> simp [hp]
 · exact False.elim (diff (hq.trans hr.symm))

end OrdinaryCommonSplit.Source
