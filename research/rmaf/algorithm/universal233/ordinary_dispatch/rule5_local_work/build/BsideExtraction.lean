import RoleBinding
namespace Universal233.Case322Extraction
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322
set_option maxRecDepth 15000

/-- Actual core labels, rather than an assumed X color on every selected arc.
A b,c anchor can contain no other core label. -/
theorem anchor_core_only_b {T S X C : Tree} {w r : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (ha : agreement T S F = true) (single : [a] ∈ F)
 (hB : B ∈ F) (bB : b ∈ B) (cB : c ∈ B) (hab : a ≠ b) :
 ∀ x, x ∈ B → x ∈ leaves C → x = b := by
 have hp := (BinaryExchange.agreement_parts T S F ha).1
 have noA := singleton_excludes_other hp single hB bB (Ne.symm hab)
 intro x xB xC
 apply Classical.byContradiction
 intro xnb
 have labels := (coreLabels x (block_labels hp hB xB)).1 xC
 have xna : x ≠ a := by intro e; subst x; exact noA xB
 have xW : x ∉ leaves (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)) := by
   simp [leaves,xna,labels.1,labels.2,xnb]
 exact original_crossing_clusters_exclude_block hnT hnS core he bC xC cC
   (by simp [leaves]) xW (by simp [leaves]) ha hB bB xB cB

/-- Parent labels are obtained from original source lookup/prefix data. -/
theorem cut_labels_parent {T U W : Tree} {q : RMAF.Vertex}
 (lookup : subtree T q = some U) (upper : subtree T q.dropLast = some W) :
 ∀ x, x ∈ leaves U → x ∈ leaves W := by
 intro x hx
 have qx : x ∈ subtreeLabels T q := by rw [source_subtree_labels lookup]; exact hx
 obtain ⟨v,hv,qv⟩ := (subtreeLabels_prefix T q x).1 qx
 have px : x ∈ subtreeLabels T q.dropLast := (subtreeLabels_prefix T q.dropLast x).2
   ⟨v,hv,(List.dropLast_prefix q).trans qv⟩
 rwa [source_subtree_labels upper] at px

/-- All literal original pendants whose parent is on the b-side of the b--c
path. Parent contains b and excludes c, so the LCA itself is excluded. -/
def bSideEdges (T : Tree) (b c : Nat) : List RMAF.Vertex :=
 (cuts T b c).filter fun q => (subtreeLabels T q.dropLast).contains b && !(subtreeLabels T q.dropLast).contains c

def bSideWithoutA (T : Tree) (a b c : Nat) : List RMAF.Vertex :=
 (bSideEdges T b c).filter fun q => !(subtreeLabels T q).contains a

theorem bSideEdges_sound {T : Tree} {b c : Nat} {q : RMAF.Vertex}
 (h : q ∈ bSideEdges T b c) : q ∈ cuts T b c ∧ b ∈ subtreeLabels T q.dropLast ∧ c ∉ subtreeLabels T q.dropLast := by
 have hh := List.mem_filter.1 h
 have pp : (subtreeLabels T q.dropLast).contains b = true ∧ (subtreeLabels T q.dropLast).contains c = false := by
   simpa only [Bool.and_eq_true,Bool.not_eq_true'] using hh.2
 refine ⟨hh.1,List.contains_iff_mem.1 pp.1,?_⟩
 intro hc
 have cc := List.contains_iff_mem.2 hc
 rw [cc] at pp
 simp at pp

/-- The b-side exclusion now covers X labels, arbitrary core S labels, and
the a leaf. It does not assume all selected descendant labels belong to X. -/
theorem selected_bside_anchor_excludes {T S X C U W : Tree} {w r q : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (selected : q ∈ bSideEdges T b c)
 (lookup : subtree T q = some U) (upper : subtree T q.dropLast = some W)
 (ha : agreement T S F = true) (single : [a] ∈ F)
 (hB : B ∈ F) (bB : b ∈ B) (cB : c ∈ B) (hab : a ≠ b) :
 ∀ x, x ∈ B → x ∉ leaves U := by
 have spec := bSideEdges_sound selected
 have bW : b ∈ leaves W := by
   have hh := spec.2.1
   rwa [source_subtree_labels upper] at hh
 have cW : c ∉ leaves W := by
   have hh := spec.2.2
   rwa [source_subtree_labels upper] at hh
 have hp := (BinaryExchange.agreement_parts T S F ha).1
 have bT := block_labels hp hB bB
 have cT := block_labels hp hB cB
 have bU : b ∉ leaves U := by
   have hh := source_label_outside_pendant spec.1 (Or.inl rfl) bT
   rwa [source_subtree_labels lookup] at hh
 have cU : c ∉ leaves U := by
   have hh := source_label_outside_pendant spec.1 (Or.inr rfl) cT
   rwa [source_subtree_labels lookup] at hh
 have coreOnly := anchor_core_only_b hnT hnS he core coreLabels bC cC ha single hB bB cB hab
 have base : subtree S (w ++ [false]) = some (.node (.node (.leaf a) X) (.leaf c)) := by rw [subtree_append he]; rfl
 have bV : b ∉ leaves (.node (.node (.leaf a) X) (.leaf c)) := by
   have nd := (subtreeLabels_sublist S w).nodup hnS
   rw [source_subtree_labels he] at nd
   exact fun h => (List.nodup_append.1 nd).2.2 b h b (by simp [leaves]) rfl
 intro x xB xU
 by_cases xX : x ∈ leaves X
 · exact original_crossing_clusters_exclude_block hnT hnS upper base
     (cut_labels_parent lookup upper x xU) bW cW (by simp [leaves,xX]) bV (by simp [leaves]) ha hB xB bB cB
 · have xnc : x ≠ c := by intro e; subst x; exact cU xU
   have xC := (coreLabels x (block_labels hp hB xB)).2 ⟨xX,xnc⟩
   have e := coreOnly x xB xC
   subst x
   exact bU xU

/-- Uniformly extracted unused-edge proof for every computed b-side arc,
including original core-rung arcs. The whole literal list remains charged. -/
theorem all_selected_bside_unused {T S X C : Tree} {w r : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (ha : agreement T S F = true) (single : [a] ∈ F)
 (hB : B ∈ F) (bB : b ∈ B) (cB : c ∈ B) (hab : a ≠ b) :
 ∀ q, q ∈ bSideEdges T b c → ∀ D, D ∈ F → BinaryExchange.mixed D (subtreeLabels T q).contains ≠ true := by
 intro q hq
 have spec := bSideEdges_sound hq
 obtain ⟨U,lookup⟩ := (cuts_spec T b c q).1 spec.1 |>.1
 obtain ⟨W,upper⟩ := valid_ancestor (show Valid T q from ⟨U,lookup⟩) (List.dropLast_prefix q)
 have noU := selected_bside_anchor_excludes hnT hnS he core coreLabels bC cC hq lookup upper ha single hB bB cB hab
 rw [source_subtree_labels lookup]
 exact anchor_unused_pendant hnT ha spec.1 lookup hB bB cB noU
end Universal233.Case322Extraction
