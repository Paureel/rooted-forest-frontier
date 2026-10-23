import CsideExtraction
namespace Universal233.Case322Extraction
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322
set_option maxRecDepth 15000

theorem anchor_other_is_X {T S X C : Tree} {w r : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (bottom sa sc sb a b c X))
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (ha : agreement T S F = true) (single : [a] ∈ F)
 (hB : B ∈ F) (bB : b ∈ B) (cB : c ∈ B) (hab : a ≠ b) :
 ∀ x, x ∈ B → x ≠ b → x ≠ c → x ∈ leaves X := by
 intro x xB xnb xnc
 apply Classical.byContradiction
 intro noX
 have xT := block_labels (BinaryExchange.agreement_parts T S F ha).1 hB xB
 have xC := (coreLabels x xT).2 ⟨noX,xnc⟩
 exact xnb (oriented_anchor_core_only_b hnT hnS he core coreLabels bC cC ha single hB bB cB hab x xB xC)

/-- Two computed c-side arcs require no unproved subtree-color record.
Only actual anchor labels are transferred to X; core labels are excluded by
an independent original-cluster obstruction. -/
theorem oriented_computed_cside_unused {T S X C U V : Tree} {w r q t : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (bottom sa sc sb a b c X))
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (hq : q ∈ cSideEdges T b c) (ht : t ∈ cSideEdges T b c) (ne : q ≠ t)
 (qU : subtree T q = some U) (tV : subtree T t = some V)
 (ha : agreement T S F = true) (single : [a] ∈ F)
 (hB : B ∈ F) (bB : b ∈ B) (cB : c ∈ B) (hab : a ≠ b) :
 (∀ D, D ∈ F → BinaryExchange.mixed D (leaves U).contains ≠ true) ∨
 (∀ D, D ∈ F → BinaryExchange.mixed D (leaves V).contains ≠ true) := by
 have otherX := anchor_other_is_X hnT hnS he core coreLabels bC cC ha single hB bB cB hab
 have hp := (BinaryExchange.agreement_parts T S F ha).1
 have bT := block_labels hp hB bB
 have cT := block_labels hp hB cB
 have qcut := (cSideEdges_sound hq).1
 have tcut := (cSideEdges_sound ht).1
 have inQX : ∀ x, x ∈ B → x ∈ leaves U → x ∈ leaves X := by
   intro x xB xU
   apply otherX x xB
   · intro e; subst x
     have no := source_label_outside_pendant qcut (Or.inl rfl) bT
     rw [source_subtree_labels qU] at no
     exact no xU
   · intro e; subst x
     have no := source_label_outside_pendant qcut (Or.inr rfl) cT
     rw [source_subtree_labels qU] at no
     exact no xU
 have inTX : ∀ x, x ∈ B → x ∈ leaves V → x ∈ leaves X := by
   intro x xB xV
   apply otherX x xB
   · intro e; subst x
     have no := source_label_outside_pendant tcut (Or.inl rfl) bT
     rw [source_subtree_labels tV] at no
     exact no xV
   · intro e; subst x
     have no := source_label_outside_pendant tcut (Or.inr rfl) cT
     rw [source_subtree_labels tV] at no
     exact no xV
 have sourceX := bottom_x_lookup he
 have cNotX := (bottom_proper hnS he).2.1
 have one : ∀ {A D W : Tree} {z : RMAF.Vertex}, subtree T z = some W → c ∈ leaves W →
   (∀ x, x ∈ leaves A → x ∈ leaves W) → (∀ y, y ∈ leaves D → y ∉ leaves W) →
   (∀ x, x ∈ B → x ∈ leaves A → x ∈ leaves X) →
   (∀ y, y ∈ B → y ∈ leaves D → y ∈ leaves X) →
   (∀ x, x ∈ B → x ∉ leaves A) ∨ (∀ y, y ∈ B → y ∉ leaves D) := by
   intro A D W z upper cW aW dW aX dX
   by_cases noA : ∀ x, x ∈ B → x ∉ leaves A
   · exact Or.inl noA
   · right
     intro y yB yD
     apply noA
     intro x xB xA
     exact original_crossing_clusters_exclude_block hnT hnS upper sourceX
       (aW x xA) cW (dW y yD) (aX x xB xA) cNotX (dX y yB yD) ha hB xB cB yB
 have noBoth : (∀ x, x ∈ B → x ∉ leaves U) ∨ (∀ y, y ∈ B → y ∉ leaves V) := by
   rcases cside_actual_lower_cluster hnT hq ht ne qU tV with ⟨W,z,up,cW,uW,vW⟩ | ⟨W,z,up,cW,vW,uW⟩
   · exact one up cW uW vW inQX inTX
   · exact (one up cW vW uW inTX inQX).symm
 rcases noBoth with noU | noV
 · exact Or.inl (anchor_unused_pendant hnT ha qcut qU hB bB cB noU)
 · exact Or.inr (anchor_unused_pendant hnT ha tcut tV hB bB cB noV)

theorem oriented_computed_typeI_cover {T S X C : Tree} {w r qa q t : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (bottom sa sc sb a b c X))
 (ch : ActualCherry T a b) (two : (cuts S a b).length = 2)
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (leafA : LeafAt T qa a) (hq : q ∈ cSideEdges T b c) (ht : t ∈ cSideEdges T b c) (ne : q ≠ t)
 (ha : agreement T S F = true) :
 ∃ P, P ∈ typeIChildren T S a b qa q t ∧ OriginalCover T S F P := by
 rcases oriented_hard2_or_b_or_bcx hnT hnS same he ch two ha with hard | singleB | ⟨singleA,B,hB,bB,cB,_⟩
 · exact ⟨pendantPartition S a b,by simp [typeIChildren],hard⟩
 · exact ⟨singletonPartition S b,by simp [typeIChildren],F,ha,Nat.le_refl _,singleton_refinement ha singleB⟩
 · obtain ⟨U,qU⟩ := ((cuts_spec T b c q).1 (cSideEdges_sound hq).1).1
   obtain ⟨V,tV⟩ := ((cuts_spec T b c t).1 (cSideEdges_sound ht).1).1
   have alt := oriented_computed_cside_unused hnT hnS he core coreLabels bC cC hq ht ne qU tV ha singleA hB bB cB
     (unordered_cherry_distinct hnT ch)
   rcases alt with uq | ut
   · refine ⟨arcPartition T [qa,q],by simp [typeIChildren],F,ha,Nat.le_refl _,?_⟩
     apply singleton_plus_unused_refines [q] ha leafA singleA
     intro z hz; have ez : z = q := by simpa using hz
     subst z; rw [source_subtree_labels qU]; exact uq
   · refine ⟨arcPartition T [qa,t],by simp [typeIChildren],F,ha,Nat.le_refl _,?_⟩
     apply singleton_plus_unused_refines [t] ha leafA singleA
     intro z hz; have ez : z = t := by simpa using hz
     subst z; rw [source_subtree_labels tV]; exact ut

/-- All source sibling orders for the incoming-LCA family. The actual core
obstruction replaces a claimed ancestor-attachment/cover field. -/
theorem oriented_ancestor_unused {T S X C W : Tree} {w r q : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (bottom sa sc sb a b c X))
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (lookup : subtree T q = some W) (bW : b ∈ leaves W) (cW : c ∈ leaves W)
 (onPath : q ∈ minimalVertices [b,c] T)
 (ha : agreement T S F = true) (single : [a] ∈ F)
 (hB : B ∈ F) (bB : b ∈ B) (cB : c ∈ B) (hab : a ≠ b) :
 ∀ D, D ∈ F → BinaryExchange.mixed D (leaves W).contains ≠ true := by
 have coreOnly := oriented_anchor_core_only_b hnT hnS he core coreLabels bC cC ha single hB bB cB hab
 have parts := BinaryExchange.agreement_parts T S F ha
 have allB : ∀ x, x ∈ B → x ∈ leaves W := by
   intro x xB
   apply Classical.byContradiction
   intro noW
   by_cases xX : x ∈ leaves X
   · exact original_crossing_clusters_exclude_block hnT hnS lookup (bottom_v_lookup he)
       cW bW noW (by simp [VC_mem]) (bottom_proper hnS he).2.2.2 (by simp [VC_mem,xX]) ha hB cB bB xB
   · have xnc : x ≠ c := by intro e; subst x; exact noW cW
     have xC := (coreLabels x (block_labels parts.1 hB xB)).2 ⟨xX,xnc⟩
     have e := coreOnly x xB xC
     subst x; exact noW bW
 have occB : q ∈ minimalVertices B T := by
   apply (minimalVertices_correct B T q).2
   apply BinaryExchange.hull_mono T [b,c] B
   · intro x hx; have e : x = b ∨ x = c := by simpa using hx
     rcases e with rfl | rfl <;> assumption
   · exact (minimalVertices_correct [b,c] T q).1 onPath
 intro D hD mixed
 obtain ⟨⟨x,xD,xW⟩,⟨y,yD,yW⟩⟩ := (BinaryExchange.mixed_iff D (leaves W).contains).1 mixed
 have yn : y ∉ leaves W := by simpa using yW
 have ne : D ≠ B := by intro e; exact yn (allB y (e ▸ yD))
 have atQ : BinaryExchange.treeAt T q = some W := by rw [source_treeAt]; exact lookup
 have occD := BinaryExchange.crossing_occupies T W q D hnT atQ (fun z hz => block_labels parts.1 hD hz)
   ⟨⟨x,xD,List.contains_iff_mem.1 xW⟩,⟨y,yD,yn⟩⟩
 have dj := BinaryExchange.pairwise_mem (fun _ _ h => BinaryExchange.disj_symm h) F parts.2.2.2.1 D B hD hB ne
 exact dj q ⟨(minimalVertices_correct D T q).1 occD,(minimalVertices_correct B T q).1 occB⟩
end Universal233.Case322Extraction
