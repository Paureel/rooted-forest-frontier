import Refinement
import OriginalGraph

namespace Universal233.HardParent
open RMAF CoreGraph Integration VertexGeometry CutRealization

theorem vertices_correct (S : Tree) (q : RMAF.Vertex) : q ∈ vertices S ↔ Valid S q := by
  induction S generalizing q with
  | leaf x =>
    cases q with
    | nil => simp [vertices,Valid,subtree]
    | cons s q => simp [vertices,Valid,subtree]
  | node l r ihl ihr =>
    cases q with
    | nil => simp [vertices,Valid,subtree,prependSide]
    | cons s q =>
      cases s
      · simpa [vertices,prependSide,Valid,subtree] using ihl q
      · simpa [vertices,prependSide,Valid,subtree] using ihr q

theorem vertices_nodup (S : Tree) : (vertices S).Nodup := by
  induction S with
  | leaf x => simp [vertices]
  | node l r ihl ihr =>
    simp [vertices,prependSide,List.nodup_append]
    constructor
    · exact List.Pairwise.map (S := fun u v : RMAF.Vertex => u ≠ v) (false :: ·)
        (by intro u v h he; exact h (List.cons.inj he).2) ihl
    · exact List.Pairwise.map (S := fun u v : RMAF.Vertex => u ≠ v) (true :: ·)
        (by intro u v h he; exact h (List.cons.inj he).2) ihr

theorem pendantOriginal_nodup (S : Tree) (a b : Nat) :
    (pendantOriginal S a b).Nodup :=
  (vertices_nodup S).filter _

theorem pendantOriginal_spec (S : Tree) (a b : Nat) (q : RMAF.Vertex) :
    q ∈ pendantOriginal S a b ↔
      Valid S q ∧ q ≠ [] ∧ q.dropLast ∈ minimalVertices [a,b] S ∧
        q ∉ minimalVertices [a,b] S := by
  simp [pendantOriginal,vertices_correct,and_assoc]

/-- The executable two-leaf hull is the unique ORIGINAL a--b path, including
both endpoints. This identifies the executable source edge list with the
directed-child definition in the retained baseline, without suppression. -/
theorem pair_minimal_path {S : Tree} (hn : (leaves S).Nodup)
    {a b : Nat} {u v : RMAF.Vertex} (hu : LeafAt S u a) (hv : LeafAt S v b)
    (w : RMAF.Vertex) : w ∈ minimalVertices [a,b] S ↔ PathAt w u v := by
  rw [minimalVertices_correct]
  have endpoints : ∀ z, selectedLeaves [a,b] S z → z = u ∨ z = v := by
    intro z hz
    obtain ⟨x,hx,hzx⟩ := (selected_decompose_label [a,b] S z).1 hz
    have hx' : x = a ∨ x = b := by simpa using hx
    rcases hx' with hx' | hx'
    · subst x; exact Or.inl (leaf_unique hn ((leafAt_selected S z a).2 hzx) hu)
    · subst x; exact Or.inr (leaf_unique hn ((leafAt_selected S z b).2 hzx) hv)
  constructor
  · rintro ⟨z,t,hz,ht,hp⟩
    rcases endpoints z hz with hz | hz <;> rcases endpoints t ht with ht | ht
    all_goals rw [hz,ht] at hp
    · have he := path_identical w u hp
      subst w; exact .endpointL u v
    · exact hp
    · exact path_sym hp
    · have he := path_identical w v hp
      subst w; exact .endpointR u v
  · intro hp
    exact ⟨u,v,(selected_at_leaf [a,b] S u a hu).2 (by simp),
      (selected_at_leaf [a,b] S v b hv).2 (by simp),hp⟩

theorem original_pendant_spec {S : Tree} (hn : (leaves S).Nodup)
    {a b : Nat} {u v : RMAF.Vertex} (hu : LeafAt S u a) (hv : LeafAt S v b)
    (q : RMAF.Vertex) : q ∈ pendantOriginal S a b ↔
      ∃ p s, q = p ++ [s] ∧ Adj S p q ∧ PathAt p u v ∧ ¬PathAt q u v := by
  rw [pendantOriginal_spec]
  constructor
  · rintro ⟨hvalid,hne,hp,ho⟩
    rcases List.eq_nil_or_concat q with h | ⟨p,s,h⟩
    · exact False.elim (hne h)
    · have he : q = p ++ [s] := by simpa only [List.concat_eq_append] using h
      refine ⟨p,s,he,⟨?_,hvalid,Or.inl ⟨s,he⟩⟩,?_,?_⟩
      · exact valid_ancestor hvalid (by rw [he]; exact List.prefix_append _ _)
      · have hpp : q.dropLast = p := by simp [he]
        exact (pair_minimal_path hn hu hv p).1 (by simpa [hpp] using hp)
      · exact fun hh => ho ((pair_minimal_path hn hu hv q).2 hh)
  · rintro ⟨p,s,he,hadj,hp,ho⟩
    refine ⟨hadj.2.1,?_,?_,?_⟩
    · rw [he]; simp
    · have hpp : q.dropLast = p := by simp [he]
      simpa [hpp] using (pair_minimal_path hn hu hv p).2 hp
    · exact fun hh => ho ((pair_minimal_path hn hu hv q).1 hh)

theorem path_prepend (p : RMAF.Vertex) {v u w : RMAF.Vertex}
    (h : PathAt v u w) : PathAt (p ++ v) (p ++ u) (p ++ w) := by
  induction p with
  | nil => exact h
  | cons s p ih => exact .down s ih

theorem cut_on_parent_descendant {q w : RMAF.Vertex} (hq : q ≠ [])
    (hw : q <+: w) : PathAt q q.dropLast w := by
  rcases List.eq_nil_or_concat q with h | ⟨p,s,h⟩
  · exact False.elim (hq h)
  · have he : q = p ++ [s] := by simpa only [List.concat_eq_append] using h
    rw [he] at hw ⊢
    obtain ⟨tail,rfl⟩ := hw
    simpa using path_prepend p (PathAt.rightLeg s (PathAt.endpointL [] tail))

theorem minimal_convex (D : List Nat) (S : Tree) :
    Convex (fun v => v ∈ minimalVertices D S) := by
  intro v u w hu hw hp
  exact (minimalVertices_correct D S v).2
    (hull_convex (selectedLeaves D S) v u w
      ((minimalVertices_correct D S u).1 hu)
      ((minimalVertices_correct D S w).1 hw) hp)

/-- A pendant head's entire descendant side is disjoint from the path hull. -/
theorem offpath_no_descendant {D : List Nat} {S : Tree} {q w : RMAF.Vertex}
    (hq : q ≠ []) (hp : q.dropLast ∈ minimalVertices D S) (ho : q ∉ minimalVertices D S)
    (hw : w ∈ minimalVertices D S) : ¬q <+: w := by
  intro hpre
  exact ho (minimal_convex D S q q.dropLast w hp hw (cut_on_parent_descendant hq hpre))

theorem pendant_incomparable {S : Tree} {a b : Nat} {q r : RMAF.Vertex}
    (hq : q ∈ pendantOriginal S a b) (hr : r ∈ pendantOriginal S a b) (hne : q ≠ r) :
    ¬q <+: r ∧ ¬r <+: q := by
  have hq' := (pendantOriginal_spec S a b q).1 hq
  have hr' := (pendantOriginal_spec S a b r).1 hr
  have one : ∀ {u v : RMAF.Vertex}, u ≠ v → u ≠ [] →
      u.dropLast ∈ minimalVertices [a,b] S → u ∉ minimalVertices [a,b] S →
      v.dropLast ∈ minimalVertices [a,b] S → ¬u <+: v := by
    intro u v hne hun hup huo hvp hp
    have hlen : u.length < v.length := by
      have he := hp.length_le
      have hn : u.length ≠ v.length := fun hh => hne (hp.eq_of_length hh)
      omega
    have hpre : u <+: v.dropLast := List.prefix_of_prefix_length_le
      hp (List.dropLast_prefix v) (by simp; omega)
    exact offpath_no_descendant hun hup huo hvp hpre
  exact ⟨one hne hq'.2.1 hq'.2.2.1 hq'.2.2.2 hr'.2.2.1,
    one hne.symm hr'.2.1 hr'.2.2.1 hr'.2.2.2 hq'.2.2.1⟩

theorem antichain_region_left {q r v : RMAF.Vertex}
    (hqr : ¬q <+: r) (hrq : ¬r <+: q) :
    Region [q,r] q v ↔ q <+: v := by
  constructor
  · exact fun h => h.1
  · intro hv
    refine ⟨hv,?_⟩
    intro p hp hpv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact List.prefix_rfl
    · rcases List.prefix_or_prefix_of_prefix hpv hv with hh | hh
      · exact False.elim (hrq hh)
      · exact False.elim (hqr hh)

theorem antichain_region_right {q r v : RMAF.Vertex}
    (hqr : ¬q <+: r) (hrq : ¬r <+: q) :
    Region [q,r] r v ↔ r <+: v := by
  constructor
  · exact fun h => h.1
  · intro hv
    refine ⟨hv,?_⟩
    intro p hp hpv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · rcases List.prefix_or_prefix_of_prefix hpv hv with hh | hh
      · exact False.elim (hqr hh)
      · exact False.elim (hrq hh)
    · exact List.prefix_rfl

theorem two_region_root {q r v : RMAF.Vertex} (hq : q ≠ []) (hr : r ≠ []) :
    Region [q,r] [] v ↔ ¬q <+: v ∧ ¬r <+: v := by
  rw [region_root [q,r] v (by intro p hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hp; rcases hp with rfl | rfl; exact hq; exact hr)]
  simp [Live]

theorem source_label_outside_pendant {S : Tree} {a b x : Nat} {q : RMAF.Vertex}
    (hq : q ∈ pendantOriginal S a b) (hx : x = a ∨ x = b) (hlabel : x ∈ leaves S) :
    x ∉ subtreeLabels S q := by
  have he := (pendantOriginal_spec S a b q).1 hq
  intro hxq
  obtain ⟨v,hv,hpre⟩ := (subtreeLabels_prefix S q x).1 hxq
  have hvm : v ∈ minimalVertices [a,b] S := (minimalVertices_terminal _ S v x hv).2 (by simpa using hx)
  exact offpath_no_descendant he.2.1 he.2.2.1 he.2.2.2 hvm hpre

theorem subtreeLabels_nonempty {S : Tree} {q : RMAF.Vertex} (hv : Valid S q) :
    subtreeLabels S q ≠ [] := by
  obtain ⟨U,hU⟩ := hv
  have he : subtreeLabels S q = leaves U := by
    induction q generalizing S with
    | nil => simp [subtree] at hU; subst U; rfl
    | cons s q ih =>
      cases S with
      | leaf x => simp [subtree] at hU
      | node l r => exact ih hU
  rw [he]
  exact leaves_nonempty U

/-- Literal original residual graph components after deleting the two original
pendant edges, with every retained degree-two vertex and original root kept. -/
structure LiteralOriginalThree (S : Tree) (q r : RMAF.Vertex) : Prop where
  actual_left : Valid S q
  actual_right : Valid S r
  nonroot_left : q ≠ []
  nonroot_right : r ≠ []
  distinct : q ≠ r
  left_component : ∀ v, ResidualWalk S [q,r] q v ↔ Valid S v ∧ q <+: v
  right_component : ∀ v, ResidualWalk S [q,r] r v ↔ Valid S v ∧ r <+: v
  root_component : ∀ v, ResidualWalk S [q,r] [] v ↔ Valid S v ∧ ¬q <+: v ∧ ¬r <+: v
  covers : ∀ v, Valid S v → ∃ c, c ∈ [[],q,r] ∧ ResidualWalk S [q,r] c v
  separated : ∀ c d, c ∈ [[],q,r] → d ∈ [[],q,r] → ResidualWalk S [q,r] c d → c = d
  leafsets : ∀ x,
    (x ∈ subtreeLabels S q ↔ ∃ v, LeafAt S v x ∧ ResidualWalk S [q,r] q v) ∧
    (x ∈ subtreeLabels S r ↔ ∃ v, LeafAt S v x ∧ ResidualWalk S [q,r] r v) ∧
    (x ∈ (leaves S).filter (fun y => !(subtreeLabels S q).contains y && !(subtreeLabels S r).contains y) ↔
      ∃ v, LeafAt S v x ∧ ResidualWalk S [q,r] [] v)
  nonempty_left : subtreeLabels S q ≠ []
  nonempty_right : subtreeLabels S r ≠ []
  nonempty_root : (leaves S).filter (fun y => !(subtreeLabels S q).contains y && !(subtreeLabels S r).contains y) ≠ []
  no_leafless : ∀ v, Valid S v → ∃ w x, LeafAt S w x ∧ ResidualWalk S [q,r] v w

theorem literalOriginalThree_construct {S : Tree} {a b : Nat} {q r : RMAF.Vertex}
    (hn : (leaves S).Nodup) (ha : a ∈ leaves S)
    (hq : q ∈ pendantOriginal S a b) (hr : r ∈ pendantOriginal S a b)
    (hne : q ≠ r) : LiteralOriginalThree S q r := by
  have hq' := (pendantOriginal_spec S a b q).1 hq
  have hr' := (pendantOriginal_spec S a b r).1 hr
  have hab := pendant_incomparable hq hr hne
  have qself : Region [q,r] q q := ⟨List.prefix_rfl,fun _ _ h => h⟩
  have rself : Region [q,r] r r := ⟨List.prefix_rfl,fun _ _ h => h⟩
  have zself : Region [q,r] [] [] := ⟨List.prefix_rfl,fun _ _ h => h⟩
  have hqc : ∀ v, ResidualWalk S [q,r] q v ↔ Valid S v ∧ q <+: v := by
    intro v
    rw [region_component (Or.inr (by simp)) hq'.1 qself,
      antichain_region_left hab.1 hab.2]
  have hrc : ∀ v, ResidualWalk S [q,r] r v ↔ Valid S v ∧ r <+: v := by
    intro v
    rw [region_component (Or.inr (by simp)) hr'.1 rself,
      antichain_region_right hab.1 hab.2]
  have hzc : ∀ v, ResidualWalk S [q,r] [] v ↔ Valid S v ∧ ¬q <+: v ∧ ¬r <+: v := by
    intro v
    rw [region_component (Or.inl rfl) (valid_root S) zself,
      two_region_root hq'.2.1 hr'.2.1]
  have hcover : ∀ v, Valid S v → ∃ c, c ∈ [[],q,r] ∧ ResidualWalk S [q,r] c v := by
    intro v hv
    by_cases hqp : q <+: v
    · exact ⟨q,by simp,(hqc v).2 ⟨hv,hqp⟩⟩
    · by_cases hrp : r <+: v
      · exact ⟨r,by simp,(hrc v).2 ⟨hv,hrp⟩⟩
      · exact ⟨[],by simp,(hzc v).2 ⟨hv,hqp,hrp⟩⟩
  have leafsets : ∀ x,
      (x ∈ subtreeLabels S q ↔ ∃ v, LeafAt S v x ∧ ResidualWalk S [q,r] q v) ∧
      (x ∈ subtreeLabels S r ↔ ∃ v, LeafAt S v x ∧ ResidualWalk S [q,r] r v) ∧
      (x ∈ (leaves S).filter (fun y => !(subtreeLabels S q).contains y && !(subtreeLabels S r).contains y) ↔
        ∃ v, LeafAt S v x ∧ ResidualWalk S [q,r] [] v) := by
    intro x
    refine ⟨?_,?_,?_⟩
    · rw [subtreeLabels_prefix]
      constructor
      · rintro ⟨v,hv,hp⟩; exact ⟨v,hv,(hqc v).2 ⟨hv.valid,hp⟩⟩
      · rintro ⟨v,hv,hw⟩; exact ⟨v,hv,((hqc v).1 hw).2⟩
    · rw [subtreeLabels_prefix]
      constructor
      · rintro ⟨v,hv,hp⟩; exact ⟨v,hv,(hrc v).2 ⟨hv.valid,hp⟩⟩
      · rintro ⟨v,hv,hw⟩; exact ⟨v,hv,((hrc v).1 hw).2⟩
    · constructor
      · intro hx
        have hx' : x ∈ leaves S ∧ x ∉ subtreeLabels S q ∧ x ∉ subtreeLabels S r := by simpa using hx
        obtain ⟨v,hv⟩ := leaf_exists hx'.1
        exact ⟨v,hv,(hzc v).2 ⟨hv.valid,
          fun hp => hx'.2.1 ((subtreeLabels_prefix S q x).2 ⟨v,hv,hp⟩),
          fun hp => hx'.2.2 ((subtreeLabels_prefix S r x).2 ⟨v,hv,hp⟩)⟩⟩
      · rintro ⟨v,hv,hw⟩
        have hp := (hzc v).1 hw
        have one : ∀ c, ¬c <+: v → x ∉ subtreeLabels S c := by
          intro c hc hx
          obtain ⟨w,hw,hwc⟩ := (subtreeLabels_prefix S c x).1 hx
          exact hc ((leaf_unique hn hw hv) ▸ hwc)
        have hqx := one q hp.2.1
        have hrx := one r hp.2.2
        simp [leafAt_label S v x hv,hqx,hrx]
  have hqne := subtreeLabels_nonempty hq'.1
  have hrne := subtreeLabels_nonempty hr'.1
  have haroot : a ∈ (leaves S).filter (fun y => !(subtreeLabels S q).contains y && !(subtreeLabels S r).contains y) := by
    have haq := source_label_outside_pendant hq (Or.inl rfl) ha
    have har := source_label_outside_pendant hr (Or.inl rfl) ha
    simp [ha,haq,har]
  have rootne : (leaves S).filter (fun y => !(subtreeLabels S q).contains y && !(subtreeLabels S r).contains y) ≠ [] := by
    intro he
    rw [he] at haroot
    exact List.not_mem_nil haroot
  have rootleaf : ∃ w x, LeafAt S w x ∧ ResidualWalk S [q,r] [] w := by
    obtain ⟨w,hw⟩ := (leafsets a).2.2.1 haroot
    exact ⟨w,a,hw⟩
  have qleaf : ∃ w x, LeafAt S w x ∧ ResidualWalk S [q,r] q w := by
    cases he : subtreeLabels S q with
    | nil => exact False.elim (hqne he)
    | cons x xs =>
      obtain ⟨w,hw⟩ := (leafsets x).1.1 (by simp [he])
      exact ⟨w,x,hw⟩
  have rleaf : ∃ w x, LeafAt S w x ∧ ResidualWalk S [q,r] r w := by
    cases he : subtreeLabels S r with
    | nil => exact False.elim (hrne he)
    | cons x xs =>
      obtain ⟨w,hw⟩ := (leafsets x).2.1.1 (by simp [he])
      exact ⟨w,x,hw⟩
  refine ⟨hq'.1,hr'.1,hq'.2.1,hr'.2.1,hne,hqc,hrc,hzc,hcover,?_,leafsets,hqne,hrne,rootne,?_⟩
  · intro c d hc hd hw
    have croots : c = [] ∨ c ∈ [q,r] := by simpa using hc
    have droots : d = [] ∨ d ∈ [q,r] := by simpa using hd
    have cself : Region [q,r] c c := ⟨List.prefix_rfl,fun _ _ h => h⟩
    have dself : Region [q,r] d d := ⟨List.prefix_rfl,fun _ _ h => h⟩
    have hreg := ((region_component croots hw.start cself).1 hw).2
    exact rooted_regions_disjoint croots droots hreg dself
  · intro v hv
    obtain ⟨c,hc,hw⟩ := hcover v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨w,x,hl,hw'⟩ := rootleaf
      exact ⟨w,x,hl,hw.reverse.trans hw'⟩
    · obtain ⟨w,x,hl,hw'⟩ := qleaf
      exact ⟨w,x,hl,hw.reverse.trans hw'⟩
    · obtain ⟨w,x,hl,hw'⟩ := rleaf
      exact ⟨w,x,hl,hw.reverse.trans hw'⟩

end Universal233.HardParent
