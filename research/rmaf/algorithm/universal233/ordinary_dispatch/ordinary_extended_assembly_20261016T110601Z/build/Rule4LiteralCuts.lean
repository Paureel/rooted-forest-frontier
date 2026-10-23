import Rule4Cover

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

def literalPartition (S : Tree) (cuts : List RMAF.Vertex) : List (List Nat) :=
  cuts.map (subtreeLabels S) ++
    [(leaves S).filter (fun x => cuts.all (fun q => !(subtreeLabels S q).contains x))]

structure OriginalAntichain (S : Tree) (cuts : List RMAF.Vertex) : Prop where
  distinct : cuts.Nodup
  actual : ∀ q, q ∈ cuts → Valid S q
  nonroot : ∀ q, q ∈ cuts → q ≠ []
  incomparable : ∀ q r, q ∈ cuts → r ∈ cuts → q ≠ r → ¬q <+: r ∧ ¬r <+: q

theorem antichain_region {S : Tree} {cuts : List RMAF.Vertex}
    (h : OriginalAntichain S cuts) {q : RMAF.Vertex} (hq : q ∈ cuts) (v : RMAF.Vertex) :
    Region cuts q v ↔ q <+: v := by
  constructor
  · exact fun hh => hh.1
  · intro hqv
    refine ⟨hqv,?_⟩
    intro p hp hpv
    by_cases he : p = q
    · subst p; exact List.prefix_rfl
    have hi := h.incomparable p q hp hq he
    rcases List.prefix_or_prefix_of_prefix hpv hqv with hh | hh
    · exact False.elim (hi.1 hh)
    · exact False.elim (hi.2 hh)

theorem antichain_component {S : Tree} {cuts : List RMAF.Vertex}
    (h : OriginalAntichain S cuts) {q : RMAF.Vertex} (hq : q ∈ cuts) (v : RMAF.Vertex) :
    ResidualWalk S cuts q v ↔ Valid S v ∧ q <+: v := by
  have hself : Region cuts q q := (antichain_region h hq q).2 List.prefix_rfl
  rw [region_component (Or.inr hq) (h.actual q hq) hself,antichain_region h hq]

theorem antichain_root_component {S : Tree} {cuts : List RMAF.Vertex}
    (h : OriginalAntichain S cuts) (v : RMAF.Vertex) :
    ResidualWalk S cuts [] v ↔ Valid S v ∧ ∀ q, q ∈ cuts → ¬q <+: v := by
  have hs : Region cuts [] [] := ⟨List.nil_prefix,fun _ _ hp => hp⟩
  rw [region_component (Or.inl rfl) (valid_root S) hs,region_root cuts v h.nonroot]
  rfl

theorem antichain_covers {S : Tree} {cuts : List RMAF.Vertex}
    (h : OriginalAntichain S cuts) (v : RMAF.Vertex) (hv : Valid S v) :
    ∃ q, q ∈ cuts ++ [[]] ∧ ResidualWalk S cuts q v := by
  by_cases hex : ∃ q, q ∈ cuts ∧ q <+: v
  · obtain ⟨q,hq,hqv⟩ := hex
    exact ⟨q,by simp [hq],(antichain_component h hq v).2 ⟨hv,hqv⟩⟩
  · exact ⟨[],by simp,(antichain_root_component h v).2
      ⟨hv,by intro q hq hqv; exact hex ⟨q,hq,hqv⟩⟩⟩

theorem antichain_separated {S : Tree} {cuts : List RMAF.Vertex}
    (h : OriginalAntichain S cuts) (q r : RMAF.Vertex)
    (hq : q ∈ cuts ++ [[]]) (hr : r ∈ cuts ++ [[]])
    (hw : ResidualWalk S cuts q r) : q = r := by
  have roots : ∀ p, p ∈ cuts ++ [[]] → p = [] ∨ p ∈ cuts := by
    intro p hp
    have hh : p ∈ cuts ∨ p = [] := by simpa using hp
    exact hh.elim Or.inr Or.inl
  have self (p) (hp : p ∈ cuts ++ [[]]) : Region cuts p p := ⟨List.prefix_rfl,fun _ _ hh => hh⟩
  have hqv : Valid S q := hw.start
  have hrr : Valid S r := hw.finish
  have hqr := ((region_component (roots q hq) hqv (self q hq)).1 hw).2
  exact rooted_regions_disjoint (roots q hq) (roots r hr) hqr (self r hr)

theorem antichain_cut_leafsets {S : Tree} {cuts : List RMAF.Vertex}
    (h : OriginalAntichain S cuts) {q : RMAF.Vertex} (hq : q ∈ cuts) (x : Nat) :
    x ∈ subtreeLabels S q ↔ ∃ v, LeafAt S v x ∧ ResidualWalk S cuts q v := by
  rw [subtreeLabels_prefix]
  constructor
  · rintro ⟨v,hv,hpre⟩; exact ⟨v,hv,(antichain_component h hq v).2 ⟨hv.valid,hpre⟩⟩
  · rintro ⟨v,hv,hw⟩; exact ⟨v,hv,((antichain_component h hq v).1 hw).2⟩

theorem antichain_root_leafsets {S : Tree} (hn : (leaves S).Nodup)
    {cuts : List RMAF.Vertex} (h : OriginalAntichain S cuts) (x : Nat) :
    x ∈ (leaves S).filter (fun x => cuts.all (fun q => !(subtreeLabels S q).contains x)) ↔
      ∃ v, LeafAt S v x ∧ ResidualWalk S cuts [] v := by
  constructor
  · intro hx
    obtain ⟨hxl,hx⟩ := List.mem_filter.1 hx
    obtain ⟨v,hv⟩ := leaf_exists hxl
    refine ⟨v,hv,(antichain_root_component h v).2 ⟨hv.valid,?_⟩⟩
    intro q hq hp
    have hout : x ∉ subtreeLabels S q := by simpa using (List.all_eq_true.1 hx) q hq
    exact hout ((subtreeLabels_prefix S q x).2 ⟨v,hv,hp⟩)
  · rintro ⟨v,hv,hw⟩
    have hs := ((antichain_root_component h v).1 hw).2
    apply List.mem_filter.2
    refine ⟨leafAt_label S v x hv,List.all_eq_true.2 ?_⟩
    intro q hq
    have hout : x ∉ subtreeLabels S q := by
      intro hx
      obtain ⟨w,hw,hwq⟩ := (subtreeLabels_prefix S q x).1 hx
      have he := leaf_unique hn hw hv
      exact hs q hq (he ▸ hwq)
    simpa using hout

theorem antichain_no_leafless {S : Tree} (hn : (leaves S).Nodup)
    {cuts : List RMAF.Vertex} (h : OriginalAntichain S cuts) {a : Nat}
    (ha : a ∈ leaves S) (hretain : ∀ q, q ∈ cuts → a ∉ subtreeLabels S q) :
    ∀ v, Valid S v → ∃ w x, LeafAt S w x ∧ ResidualWalk S cuts v w := by
  intro v hv
  obtain ⟨q,hq,hqv⟩ := antichain_covers h v hv
  have hroots : q ∈ cuts ∨ q = [] := by simpa using hq
  have leaf : ∃ w x, LeafAt S w x ∧ ResidualWalk S cuts q w := by
    rcases hroots with hq | rfl
    · have hne := subtreeLabels_nonempty (h.actual q hq)
      obtain ⟨x,hx⟩ := nonempty_witness (subtreeLabels S q) hne
      obtain ⟨w,hw,hwalk⟩ := (antichain_cut_leafsets h hq x).1 hx
      exact ⟨w,x,hw,hwalk⟩
    · have hin : a ∈ (leaves S).filter (fun x => cuts.all (fun q => !(subtreeLabels S q).contains x)) := by
        apply List.mem_filter.2
        exact ⟨ha,List.all_eq_true.2 (by intro q hq; simpa using hretain q hq)⟩
      obtain ⟨w,hw,hwalk⟩ := (antichain_root_leafsets hn h a).1 hin
      exact ⟨w,a,hw,hwalk⟩
  obtain ⟨w,x,hw,hwalk⟩ := leaf
  exact ⟨w,x,hw,hqv.reverse.trans hwalk⟩

theorem pendant_antichain (S : Tree) (a b : Nat) :
    OriginalAntichain S (pendantOriginal S a b) := by
  exact ⟨pendantOriginal_nodup S a b,
    by intro q hq; exact ((pendantOriginal_spec S a b q).1 hq).1,
    by intro q hq; exact ((pendantOriginal_spec S a b q).1 hq).2.1,
    by intro q r hq hr hne; exact pendant_incomparable hq hr hne⟩

/-- Exact ALL-outgoing-arcs literal source regions, including every suppressed
vertex and a leaf in every residual region. Exact cost is cut list length. -/
theorem all_pendant_literal_regions {S : Tree} (hn : (leaves S).Nodup)
    {a b : Nat} (ha : a ∈ leaves S) :
    let cuts := pendantOriginal S a b
    (literalPartition S cuts).length = cuts.length + 1 ∧
    (∀ v, Valid S v → ∃ q, q ∈ cuts ++ [[]] ∧ ResidualWalk S cuts q v) ∧
    (∀ q r, q ∈ cuts ++ [[]] → r ∈ cuts ++ [[]] → ResidualWalk S cuts q r → q = r) ∧
    (∀ q, q ∈ cuts → ∀ x, x ∈ subtreeLabels S q ↔ ∃ v, LeafAt S v x ∧ ResidualWalk S cuts q v) ∧
    (∀ v, Valid S v → ∃ w x, LeafAt S w x ∧ ResidualWalk S cuts v w) := by
  have h := pendant_antichain S a b
  exact ⟨by simp [literalPartition],antichain_covers h,antichain_separated h,
    by intro q hq x; exact antichain_cut_leafsets h hq x,
    antichain_no_leafless hn h ha (by intro q hq; exact source_label_outside_pendant hq (Or.inl rfl) ha)⟩
end Universal233.Rule4
