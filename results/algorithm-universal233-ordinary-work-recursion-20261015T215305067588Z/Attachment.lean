import Rule5Case321
namespace Universal233.Rule5Classification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local

/-- A disjoint original component cannot cross an original pendant edge
whose tail is in the selected X cherry path. No AF or exchange is assumed. -/
theorem disjoint_region_constant {T : Tree} {X C : List Nat} {p q : Nat}
 {u : RMAF.Vertex} (hn : (leaves T).Nodup)
 (hpX : p ∈ X) (hqX : q ∈ X)
 (dj : BinaryExchange.Disj T X C)
 (labs : ∀ x, x ∈ C → x ∈ leaves T)
 (hu : u ∈ cuts T p q) :
 ∀ x y, x ∈ C → y ∈ C → (x ∈ subtreeLabels T u ↔ y ∈ subtreeLabels T u) := by
 have us := (cuts_spec T p q u).1 hu
 have parentX : u.dropLast ∈ minimalVertices X T := executable_span_monotone T [p,q] X
   (by intro x hx; have hh : x = p ∨ x = q := by simpa using hx
       rcases hh with rfl | rfl <;> assumption) _ us.2.2.1
 have one : ∀ x y, x ∈ C → y ∈ C → x ∈ subtreeLabels T u → y ∈ subtreeLabels T u := by
   intro x y xC yC xu
   apply Classical.byContradiction
   intro yn
   obtain ⟨a,ha,hpa⟩ := (subtreeLabels_prefix T u x).1 xu
   obtain ⟨b,hb⟩ := leaf_exists (labs y yC)
   have npb : ¬u <+: b := fun h => yn ((subtreeLabels_prefix T u y).2 ⟨b,hb,h⟩)
   have parentC : u.dropLast ∈ minimalVertices C T := by
     apply (minimalVertices_correct C T _).2
     exact ⟨a,b,(selected_at_leaf C T a x ha).2 xC,(selected_at_leaf C T b y hb).2 yC,
       cut_crossing_path us.2.1 hpa npb⟩
   exact dj u.dropLast ⟨(minimalVertices_correct X T _).1 parentX,(minimalVertices_correct C T _).1 parentC⟩
 exact fun x y hx hy => ⟨one x y hx hy,one y x hy hx⟩

theorem prunedCherry_selected {D : List Nat} {T : Tree} {p q : Nat}
 (hc : PrunedCherry D p q T) : p ∈ D ∧ q ∈ D := by
 induction hc with
 | fork hl hr => exact ⟨((HardParent.restrict_mem hl p).1 (by simp [leaves])).2,
     ((HardParent.restrict_mem hr q).1 (by simp [leaves])).2⟩
 | forkSwap hl hr => exact ⟨((HardParent.restrict_mem hr p).1 (by simp [leaves])).2,
     ((HardParent.restrict_mem hl q).1 (by simp [leaves])).2⟩
 | left _ _ _ ih => exact ih
 | right _ _ _ ih => exact ih

/-- Two actual outgoing pendants must be exactly the two other disjoint
original partition blocks. Root-side outside labels are ruled out by the
same original graph argument; they are not silently charged as cuts. -/
theorem actual_two_pendant_attachment {T : Tree} {X Y Z : List Nat}
 {p q : Nat} {u v : RMAF.Vertex}
 (hn : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,Y,Z] = true)
 (he : pairwiseEmbeddings T [X,Y,Z] = true)
 (ch : PrunedCherry X p q T) (hc : cuts T p q = [u,v]) :
 (((∀ x, x ∈ subtreeLabels T u ↔ x ∈ Y) ∧ (∀ x, x ∈ subtreeLabels T v ↔ x ∈ Z)) ∨
  ((∀ x, x ∈ subtreeLabels T u ↔ x ∈ Z) ∧ (∀ x, x ∈ subtreeLabels T v ↔ x ∈ Y))) ∧
 (∀ x, x ∈ coreLabels T p q ↔ x ∈ X) := by
 have um : u ∈ cuts T p q := by simp [hc]
 have vm : v ∈ cuts T p q := by simp [hc]
 have unv : u ≠ v := by
   have nd := pendantOriginal_nodup T p q
   change (cuts T p q).Nodup at nd
   rw [hc] at nd
   simpa using nd
 have cutdj := pendant_labelsets_disjoint hn um vm unv
 have part := (executable_pairwiseEmbeddings T [X,Y,Z]).1 he
 have djXY : BinaryExchange.Disj T X Y := (List.pairwise_cons.1 part).1 Y (by simp)
 have djXZ : BinaryExchange.Disj T X Z := (List.pairwise_cons.1 part).1 Z (by simp)
 have selected := prunedCherry_selected ch
 have excluded := prunedCherry_excluded ch
 have blocks : ∀ C, C ∈ [X,Y,Z] → ∀ x, x ∈ C → x ∈ leaves T := by
   intro C hC x hx; exact block_labels hp hC hx
 have belong {r : RMAF.Vertex} (hr : r ∈ cuts T p q) :
     ∀ x, x ∈ subtreeLabels T r → x ∈ Y ∨ x ∈ Z := by
   intro x hx
   have rs := (cuts_spec T p q r).1 hr
   have nx : x ∉ X := excluded r rs.2.1 rs.2.2.1 rs.2.2.2 x hx
   have xl := (subtreeLabels_sublist T r).subset hx
   obtain ⟨B,hB,hxB⟩ := partitionCheck_covers (leaves T) [X,Y,Z] hp x xl
   have casesB : B = X ∨ B = Y ∨ B = Z := by simpa using hB
   rcases casesB with rfl | rfl | rfl
   · exact False.elim (nx hxB)
   · exact Or.inl hxB
   · exact Or.inr hxB
 have entire {r : RMAF.Vertex} (hr : r ∈ cuts T p q) :
     Y ⊆ subtreeLabels T r ∨ Z ⊆ subtreeLabels T r := by
   obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ (subtreeLabels_nonempty ((cuts_spec T p q r).1 hr).1)
   rcases belong hr x hx with xy | xz
   · left
     intro y hy
     exact (disjoint_region_constant hn selected.1 selected.2 djXY (blocks Y (by simp)) hr x y xy hy).1 hx
   · right
     intro z hz
     exact (disjoint_region_constant hn selected.1 selected.2 djXZ (blocks Z (by simp)) hr x z xz hz).1 hx
 have yne := RestrictionBridge.checked_nonempty (leaves T) [X,Y,Z] hp Y (by simp)
 have zne := RestrictionBridge.checked_nonempty (leaves T) [X,Y,Z] hp Z (by simp)
 have finish (yu : Y ⊆ subtreeLabels T u) (zv : Z ⊆ subtreeLabels T v) :
     (∀ x, x ∈ subtreeLabels T u ↔ x ∈ Y) ∧ (∀ x, x ∈ subtreeLabels T v ↔ x ∈ Z) := by
   constructor
   · intro x; constructor
     · intro xu; rcases belong um x xu with xy | xz
       · exact xy
       · exact False.elim (cutdj x xu (zv xz))
     · exact fun hx => yu hx
   · intro x; constructor
     · intro xv; rcases belong vm x xv with xy | xz
       · exact False.elim (cutdj x (yu xy) xv)
       · exact xz
     · exact fun hx => zv hx
 have finishSwap (zu : Z ⊆ subtreeLabels T u) (yv : Y ⊆ subtreeLabels T v) :
     (∀ x, x ∈ subtreeLabels T u ↔ x ∈ Z) ∧ (∀ x, x ∈ subtreeLabels T v ↔ x ∈ Y) := by
   constructor
   · intro x; constructor
     · intro xu; rcases belong um x xu with xy | xz
       · exact False.elim (cutdj x xu (yv xy))
       · exact xz
     · exact fun hx => zu hx
   · intro x; constructor
     · intro xv; rcases belong vm x xv with xy | xz
       · exact xy
       · exact False.elim (cutdj x (zu xz) xv)
     · exact fun hx => yv hx
 constructor
 · rcases entire um with yu | zu <;> rcases entire vm with yv | zv
   · obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil Y yne
     exact False.elim (cutdj x (yu hx) (yv hx))
   · exact Or.inl (finish yu zv)
   · exact Or.inr (finishSwap zu yv)
   · obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil Z zne
     exact False.elim (cutdj x (zu hx) (zv hx))
 · intro x; constructor
   · intro hx
     obtain ⟨xl,notcuts⟩ := (mem_core T p q x).1 hx
     obtain ⟨B,hB,hxB⟩ := partitionCheck_covers (leaves T) [X,Y,Z] hp x xl
     have casesB : B = X ∨ B = Y ∨ B = Z := by simpa using hB
     rcases casesB with rfl | rfl | rfl
     · exact hxB
     · rcases entire um with yu | zu
       · exact False.elim (notcuts u um (yu hxB))
       · rcases entire vm with yv | zv
         · exact False.elim (notcuts v vm (yv hxB))
         · obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil Z zne
           exact False.elim (cutdj z (zu hz) (zv hz))
     · rcases entire um with yu | zu
       · rcases entire vm with yv | zv
         · obtain ⟨y,hy⟩ := List.exists_mem_of_ne_nil Y yne
           exact False.elim (cutdj y (yu hy) (yv hy))
         · exact False.elim (notcuts v vm (zv hxB))
       · exact False.elim (notcuts u um (zu hxB))
   · intro hx
     refine (mem_core T p q x).2 ⟨blocks X (by simp) x hx,?_⟩
     intro r hr hxr
     have rs := (cuts_spec T p q r).1 hr
     exact excluded r rs.2.1 rs.2.2.1 rs.2.2.2 x hxr hx

end Universal233.Rule5Classification
