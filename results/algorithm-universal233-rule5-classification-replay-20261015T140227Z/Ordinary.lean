import Safety
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

/-- Original child edges, in original vertex traversal order. No upward edge. -/
def cuts (S : Tree) (a b : Nat) := pendantOriginal S a b

def coreLabels (S : Tree) (a b : Nat) : List Nat :=
 (leaves S).filter fun x => !((cuts S a b).map (subtreeLabels S)).flatten.contains x

def pendantPartition (S : Tree) (a b : Nat) : List (List Nat) :=
 (cuts S a b).map (subtreeLabels S) ++ [coreLabels S a b]

def componentRoots (S : Tree) (a b : Nat) : List RMAF.Vertex := cuts S a b ++ [[]]

theorem cuts_spec (S : Tree) (a b : Nat) (q : RMAF.Vertex) :
 q ∈ cuts S a b ↔ Valid S q ∧ q ≠ [] ∧
 q.dropLast ∈ minimalVertices [a,b] S ∧ q ∉ minimalVertices [a,b] S := pendantOriginal_spec S a b q

theorem partition_length (S : Tree) (a b : Nat) :
 (pendantPartition S a b).length = (cuts S a b).length + 1 := by simp [pendantPartition]

theorem pendant_region {S : Tree} {a b : Nat} {q v : RMAF.Vertex}
 (hq : q ∈ cuts S a b) : Region (cuts S a b) q v ↔ q <+: v := by
 constructor
 · exact fun h => h.1
 · intro hv
   refine ⟨hv,?_⟩
   intro r hr hrv
   by_cases e : r = q
   · simpa [e]
   · have inc := pendant_incomparable hr hq e
     rcases List.prefix_or_prefix_of_prefix hrv hv with h | h
     · exact False.elim (inc.1 h)
     · exact False.elim (inc.2 h)

theorem cut_component {S : Tree} {a b : Nat} {q : RMAF.Vertex}
 (hq : q ∈ cuts S a b) (v : RMAF.Vertex) :
 ResidualWalk S (cuts S a b) q v ↔ Valid S v ∧ q <+: v := by
 have hs := (cuts_spec S a b q).1 hq
 rw [region_component (Or.inr hq) hs.1 ⟨List.prefix_rfl,fun _ _ h => h⟩,
   pendant_region hq]

theorem root_component (S : Tree) (a b : Nat) (v : RMAF.Vertex) :
 ResidualWalk S (cuts S a b) [] v ↔ Valid S v ∧ Live (cuts S a b) v := by
 rw [region_component (Or.inl rfl) (valid_root S) ⟨List.prefix_rfl,fun _ _ h => h⟩,
   region_root _ _ (fun q hq => ((cuts_spec S a b q).1 hq).2.1)]

theorem original_cover (S : Tree) (a b : Nat) (v : RMAF.Vertex) (hv : Valid S v) :
 ∃ r, r ∈ componentRoots S a b ∧ ResidualWalk S (cuts S a b) r v := by
 by_cases h : ∃ q, q ∈ cuts S a b ∧ q <+: v
 · obtain ⟨q,hq,hv'⟩ := h
   exact ⟨q,by simp [componentRoots,hq],(cut_component hq v).2 ⟨hv,hv'⟩⟩
 · exact ⟨[],by simp [componentRoots],(root_component S a b v).2
     ⟨hv,fun q hq hp => h ⟨q,hq,hp⟩⟩⟩

theorem roots_separated {S : Tree} {a b : Nat} {r s : RMAF.Vertex}
 (hr : r ∈ componentRoots S a b) (hs : s ∈ componentRoots S a b)
 (hw : ResidualWalk S (cuts S a b) r s) : r = s := by
 have rr : r = [] ∨ r ∈ cuts S a b := by simpa [componentRoots,or_comm] using hr
 have ss : s = [] ∨ s ∈ cuts S a b := by simpa [componentRoots,or_comm] using hs
 exact rooted_regions_disjoint rr ss
   ((region_component rr hw.start ⟨List.prefix_rfl,fun _ _ h => h⟩).1 hw).2
   ⟨List.prefix_rfl,fun _ _ h => h⟩

theorem cut_leafset {S : Tree} {a b : Nat} {q : RMAF.Vertex}
 (hq : q ∈ cuts S a b) (x : Nat) :
 x ∈ subtreeLabels S q ↔ ∃ v, LeafAt S v x ∧ ResidualWalk S (cuts S a b) q v := by
 rw [subtreeLabels_prefix]
 constructor
 · rintro ⟨v,hv,hp⟩; exact ⟨v,hv,(cut_component hq v).2 ⟨hv.valid,hp⟩⟩
 · rintro ⟨v,hv,hw⟩; exact ⟨v,hv,((cut_component hq v).1 hw).2⟩

theorem mem_core (S : Tree) (a b x : Nat) :
 x ∈ coreLabels S a b ↔ x ∈ leaves S ∧ ∀ q, q ∈ cuts S a b → x ∉ subtreeLabels S q := by
 simp [coreLabels,List.mem_flatten,List.mem_map]

theorem root_leafset {S : Tree} {a b : Nat} (hn : (leaves S).Nodup) (x : Nat) :
 x ∈ coreLabels S a b ↔ ∃ v, LeafAt S v x ∧ ResidualWalk S (cuts S a b) [] v := by
 rw [mem_core]
 constructor
 · rintro ⟨hx,hall⟩
   obtain ⟨v,hv⟩ := leaf_exists hx
   exact ⟨v,hv,(root_component S a b v).2 ⟨hv.valid,fun q hq hp =>
     hall q hq ((subtreeLabels_prefix S q x).2 ⟨v,hv,hp⟩)⟩⟩
 · rintro ⟨v,hv,hw⟩
   refine ⟨leafAt_label S v x hv,?_⟩
   intro q hq hx
   obtain ⟨w,hw',hp⟩ := (subtreeLabels_prefix S q x).1 hx
   have e := leaf_unique hn hw' hv
   exact ((root_component S a b v).1 hw).2 q hq (e ▸ hp)

theorem endpoint_core {S : Tree} {a b x : Nat} (hx : x = a ∨ x = b)
 (hl : x ∈ leaves S) : x ∈ coreLabels S a b := by
 exact (mem_core S a b x).2 ⟨hl,fun _ hq => source_label_outside_pendant hq hx hl⟩

theorem no_leafless {S : Tree} {a b : Nat} (hn : (leaves S).Nodup) (ha : a ∈ leaves S)
 (v : RMAF.Vertex) (hv : Valid S v) :
 ∃ w x, LeafAt S w x ∧ ResidualWalk S (cuts S a b) v w := by
 obtain ⟨r,hr,hw⟩ := original_cover S a b v hv
 have casesr : r ∈ cuts S a b ∨ r = [] := by simpa [componentRoots] using hr
 rcases casesr with hcut | rfl
 · have ne := subtreeLabels_nonempty ((cuts_spec S a b r).1 hcut).1
   obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ ne
   obtain ⟨w,hl,hw'⟩ := (cut_leafset hcut x).1 hx
   exact ⟨w,x,hl,hw.reverse.trans hw'⟩
 · obtain ⟨w,hl,hw'⟩ := (root_leafset hn a).1 (endpoint_core (Or.inl rfl) ha)
   exact ⟨w,a,hl,hw.reverse.trans hw'⟩

/-- This proof is universal in the number of original pendant cuts. -/
theorem actual_pendant_safety {T S : Tree} {F : List (List Nat)}
 (hn : (leaves S).Nodup) (ha : agreement T S F = true)
 {p : RMAF.Vertex} {a b : Nat} (hc : CherryAt T p a b) :
 [a] ∈ F ∨ [b] ∈ F ∨ Refines F (pendantPartition S a b) := by
 rcases actual_cherry_endpoint_alternative ha hc with hs | hs | ⟨B,hB,haB,hbB⟩
 · exact Or.inl hs
 · exact Or.inr (Or.inl hs)
 · right; right
   have mono : ∀ q, q ∈ cuts S a b → ∀ C, C ∈ F → ∀ x y, x ∈ C → y ∈ C →
       (x ∈ subtreeLabels S q ↔ y ∈ subtreeLabels S q) := by
     intro q hq
     have h := (cuts_spec S a b q).1 hq
     exact agreement_respects_pendant hn ha hc hB haB hbB h.2.1 h.2.2.1 h.2.2.2
   intro C hC
   have ne := (agreement_graph_factors T S F ha).2.2 C hC
   obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil C ne
   by_cases hit : ∃ q, q ∈ cuts S a b ∧ x ∈ subtreeLabels S q
   · obtain ⟨q,hq,hxq⟩ := hit
     exact ⟨subtreeLabels S q,List.mem_append_left _ (List.mem_map.2 ⟨q,hq,rfl⟩),
       fun y hy => (mono q hq C hC x y hx hy).1 hxq⟩
   · refine ⟨coreLabels S a b,by simp [pendantPartition],?_⟩
     intro y hy
     exact (mem_core S a b y).2 ⟨block_labels (source_agreement_checks ha).1 hC hy,
       fun q hq hyq => hit ⟨q,hq,(mono q hq C hC x y hx hy).2 hyq⟩⟩

/-- t>=3 is a priority guard; the geometry theorem itself needs no such bound. -/
theorem actual_high_safety {T S : Tree} {F : List (List Nat)}
 (hn : (leaves S).Nodup) (ha : agreement T S F = true)
 {p : RMAF.Vertex} {a b : Nat} (hc : CherryAt T p a b)
 (_high : 3 ≤ (cuts S a b).length) :
 [a] ∈ F ∨ [b] ∈ F ∨ Refines F (pendantPartition S a b) := actual_pendant_safety hn ha hc
end Universal233.CherryBranching
