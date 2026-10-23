import OrientedExchange
namespace Universal233.Case322Extraction
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322
set_option maxRecDepth 15000
theorem oriented_anchor_core_only_b {T S X C : Tree} {w r : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (bottom sa sc sb a b c X))
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
 have xW : x ∉ leaves (bottom sa sc sb a b c X) := by
   simp [bottom_mem,xna,labels.1,labels.2,xnb]
 exact original_crossing_clusters_exclude_block hnT hnS core he bC xC cC
   (by simp [bottom_mem]) xW (by simp [bottom_mem]) ha hB bB xB cB

/-- The b-side exclusion now covers X labels, arbitrary core S labels, and
the a leaf. It does not assume all selected descendant labels belong to X. -/
theorem oriented_selected_bside_anchor_excludes {T S X C U W : Tree} {w r q : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (bottom sa sc sb a b c X))
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
 have coreOnly := oriented_anchor_core_only_b hnT hnS he core coreLabels bC cC ha single hB bB cB hab
 have base := bottom_v_lookup he
 have bV := (bottom_proper hnS he).2.2.2
 intro x xB xU
 by_cases xX : x ∈ leaves X
 · exact original_crossing_clusters_exclude_block hnT hnS upper base
     (cut_labels_parent lookup upper x xU) bW cW (by simp [VC_mem,xX]) bV (by simp [VC_mem]) ha hB xB bB cB
 · have xnc : x ≠ c := by intro e; subst x; exact cU xU
   have xC := (coreLabels x (block_labels hp hB xB)).2 ⟨xX,xnc⟩
   have e := coreOnly x xB xC
   subst x
   exact bU xU

/-- Uniformly extracted unused-edge proof for every computed b-side arc,
including original core-rung arcs. The whole literal list remains charged. -/
theorem oriented_all_selected_bside_unused {T S X C : Tree} {w r : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (bottom sa sc sb a b c X))
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
 have noU := oriented_selected_bside_anchor_excludes hnT hnS he core coreLabels bC cC hq lookup upper ha single hB bB cB hab
 rw [source_subtree_labels lookup]
 exact anchor_unused_pendant hnT ha spec.1 lookup hB bB cB noU

/-- Complete computed typeII original-AF cover for arbitrary source sibling
orders and arbitrary selected core rungs. No per-arc X-color field remains. -/
theorem oriented_computed_typeII_cover {T S X C : Tree} {w r qa : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (bottom sa sc sb a b c X))
 (ch : ActualCherry T a b) (two : (cuts S a b).length = 2)
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (leafA : LeafAt T qa a) (ha : agreement T S F = true) :
 ∃ P, P ∈ typeIIChildren T S a b qa (bSideWithoutA T a b c) ∧ OriginalCover T S F P := by
 rcases oriented_hard2_or_b_or_bcx hnT hnS same he ch two ha with hard | singleB | ⟨singleA,B,hB,bB,cB,_⟩
 · exact ⟨pendantPartition S a b,by simp [typeIIChildren],hard⟩
 · exact ⟨singletonPartition S b,by simp [typeIIChildren],F,ha,Nat.le_refl _,singleton_refinement ha singleB⟩
 · refine ⟨arcPartition T (qa :: bSideWithoutA T a b c),by simp [typeIIChildren],F,ha,Nat.le_refl _,?_⟩
   apply singleton_plus_unused_refines _ ha leafA singleA
   intro q hq
   exact oriented_all_selected_bside_unused hnT hnS he core coreLabels bC cC ha singleA hB bB cB
     (unordered_cherry_distinct hnT ch) q (List.mem_filter.1 hq).1
end Universal233.Case322Extraction
