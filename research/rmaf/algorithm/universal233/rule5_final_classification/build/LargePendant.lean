import OutsideCore
namespace Universal233.Rule5Classification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local

theorem two_leaf_alltrue {a b x y : Nat} {f : Nat → Bool}
 (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) (ne : x ≠ y)
 (fx : f x = true) (fy : f y = true) : f a = true ∧ f b = true := by
 rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all

/-- Every nontrivial rooted cluster of a caterpillar contains the bottom
cherry. The colors are arbitrary; this is independent of Rule5 or an AF. -/
theorem caterpillar_cluster_bottom {U : Tree} {p q x y : Nat} {f : Nat → Bool}
 (cat : Caterpillar U) (ch : HasCherry p q U)
 (cl : BinaryExchange.Cluster (fun _ => True) f U)
 (hx : x ∈ leaves U) (hy : y ∈ leaves U) (ne : x ≠ y)
 (fx : f x = true) (fy : f y = true) : f p = true ∧ f q = true := by
 induction cat generalizing p q x y with
 | leaf a =>
   have ex : x = a := by simpa [leaves] using hx
   have ey : y = a := by simpa [leaves] using hy
   exact False.elim (ne (ex.trans ey.symm))
 | @left a U cat ih =>
   cases U with
   | leaf b =>
     have hxy := two_leaf_alltrue (by simpa [leaves] using hx) (by simpa [leaves] using hy) ne fx fy
     have hp := hasCherry_labels ch
     have pp : p = a ∨ p = b := by simpa [leaves] using hp.1
     have qq : q = a ∨ q = b := by simpa [leaves] using hp.2
     exact ⟨pp.elim (fun e => e ▸ hxy.1) (fun e => e ▸ hxy.2),
       qq.elim (fun e => e ▸ hxy.1) (fun e => e ▸ hxy.2)⟩
   | node l r =>
     cases ch with
     | left h => cases h
     | right ch =>
       cases cl with
       | allTrue h => exact ⟨h p (List.mem_append_right _ (hasCherry_labels ch).1) trivial,
           h q (List.mem_append_right _ (hasCherry_labels ch).2) trivial⟩
       | allFalse h => have e := h x hx trivial; rw [fx] at e; contradiction
       | left h noR =>
         have ex : x = a := by
           rcases List.mem_append.1 hx with hl | hr
           · simpa [leaves] using hl
           · have e := noR x hr trivial; rw [fx] at e; contradiction
         have ey : y = a := by
           rcases List.mem_append.1 hy with hl | hr
           · simpa [leaves] using hl
           · have e := noR y hr trivial; rw [fy] at e; contradiction
         exact False.elim (ne (ex.trans ey.symm))
       | right noL hr =>
         have xR : x ∈ leaves (.node l r) := by
           rcases List.mem_append.1 hx with hl | hr
           · have e := noL x hl trivial; rw [fx] at e; contradiction
           · exact hr
         have yR : y ∈ leaves (.node l r) := by
           rcases List.mem_append.1 hy with hl | hr
           · have e := noL y hl trivial; rw [fy] at e; contradiction
           · exact hr
         exact ih ch hr xR yR ne fx fy
 | @right a U cat ih =>
   cases U with
   | leaf b =>
     have hxy := two_leaf_alltrue (by simpa [leaves] using hx) (by simpa [leaves] using hy) ne fx fy
     have hp := hasCherry_labels ch
     have pp : p = b ∨ p = a := by simpa [leaves] using hp.1
     have qq : q = b ∨ q = a := by simpa [leaves] using hp.2
     exact ⟨pp.elim (fun e => e ▸ hxy.1) (fun e => e ▸ hxy.2),
       qq.elim (fun e => e ▸ hxy.1) (fun e => e ▸ hxy.2)⟩
   | node l r =>
     cases ch with
     | right h => cases h
     | left ch =>
       cases cl with
       | allTrue h => exact ⟨h p (List.mem_append_left _ (hasCherry_labels ch).1) trivial,
           h q (List.mem_append_left _ (hasCherry_labels ch).2) trivial⟩
       | allFalse h => have e := h x hx trivial; rw [fx] at e; contradiction
       | right noL h =>
         have ex : x = a := by
           rcases List.mem_append.1 hx with hl | hr
           · have e := noL x hl trivial; rw [fx] at e; contradiction
           · simpa [leaves] using hr
         have ey : y = a := by
           rcases List.mem_append.1 hy with hl | hr
           · have e := noL y hl trivial; rw [fy] at e; contradiction
           · simpa [leaves] using hr
         exact False.elim (ne (ex.trans ey.symm))
       | left hl noR =>
         have xL : x ∈ leaves (.node l r) := by
           rcases List.mem_append.1 hx with hl | hr
           · exact hl
           · have e := noR x hr trivial; rw [fx] at e; contradiction
         have yL : y ∈ leaves (.node l r) := by
           rcases List.mem_append.1 hy with hl | hr
           · exact hl
           · have e := noR y hr trivial; rw [fy] at e; contradiction
         exact ih ch hl xL yL ne fx fy

theorem caterpillar_iso {U V : Tree} (h : RootedIso U V) (hc : Caterpillar U) : Caterpillar V := by
 induction h with
 | leaf x => exact .leaf x
 | straight h1 h2 ih1 ih2 =>
   cases hc with
   | left x hc => cases h1; exact .left x (ih2 hc)
   | right x hc => cases h2; exact .right x (ih1 hc)
 | swapped h1 h2 ih1 ih2 =>
   cases hc with
   | left x hc => cases h1; exact .right x (ih2 hc)
   | right x hc => cases h2; exact .left x (ih1 hc)

theorem restrict_original_subtree {S U : Tree} {e : RMAF.Vertex}
 (hn : (leaves S).Nodup) (hU : subtree S e = some U) : restrict (leaves U) S = some U := by
 induction e generalizing S with
 | nil =>
   have e : S = U := Option.some.inj hU
   subst S
   exact restrict_of_contains U (leaves U) (by simp)
 | cons s e ih =>
   cases S with
   | leaf x => simp [subtree] at hU
   | node l r =>
     obtain ⟨hnl,hnr,dj⟩ := List.nodup_append.1 hn
     cases s
     · have hl : subtree l e = some U := hU
       have inside : leaves U ⊆ leaves l := by
         rw [←source_subtree_labels hl]
         exact (subtreeLabels_sublist l e).subset
       have noR : restrict (leaves U) r = none := (BinaryExchange.restrict_none_iff _ _).2
         (by intro x hx hm; exact dj x (inside hm) x hx rfl)
       simp [restrict,ih hnl hl,noR]
     · have hr : subtree r e = some U := hU
       have inside : leaves U ⊆ leaves r := by
         rw [←source_subtree_labels hr]
         exact (subtreeLabels_sublist r e).subset
       have noL : restrict (leaves U) l = none := (BinaryExchange.restrict_none_iff _ _).2
         (by intro x hx hm; exact dj x hx x (inside hm) rfl)
       simp [restrict,ih hnr hr,noL]

/-- A true-colored cluster containing two selected leaves yields an actual
original subtree containing those leaves and excluding every selected
false-colored leaf. Unary original paths remain in the witness address. -/
theorem cluster_actual_subtree {T : Tree} {B : List Nat} {f : Nat → Bool} {x y z : Nat}
 (cl : BinaryExchange.Cluster (fun t => t ∈ B) f T)
 (hx : x ∈ leaves T) (hy : y ∈ leaves T) (xB : x ∈ B) (yB : y ∈ B) (zB : z ∈ B)
 (fx : f x = true) (fy : f y = true) (fz : f z = false) :
 ∃ e W, subtree T e = some W ∧ x ∈ leaves W ∧ y ∈ leaves W ∧ z ∉ leaves W := by
 induction cl with
 | allTrue h =>
   exact ⟨[],_,rfl,hx,hy,fun hz => by have no := h z hz zB; rw [fz] at no; contradiction⟩
 | allFalse h => have no := h x hx xB; rw [fx] at no; contradiction
 | @left l r cl noR ih =>
   have xL : x ∈ leaves l := by
     rcases List.mem_append.1 hx with hm | hm
     · exact hm
     · have no := noR x hm xB; rw [fx] at no; contradiction
   have yL : y ∈ leaves l := by
     rcases List.mem_append.1 hy with hm | hm
     · exact hm
     · have no := noR y hm yB; rw [fy] at no; contradiction
   obtain ⟨e,W,hW,hxW,hyW,noZ⟩ := ih xL yL
   exact ⟨false::e,W,hW,hxW,hyW,noZ⟩
 | @right l r noL cl ih =>
   have xR : x ∈ leaves r := by
     rcases List.mem_append.1 hx with hm | hm
     · have no := noL x hm xB; rw [fx] at no; contradiction
     · exact hm
   have yR : y ∈ leaves r := by
     rcases List.mem_append.1 hy with hm | hm
     · have no := noL y hm yB; rw [fy] at no; contradiction
     · exact hm
   obtain ⟨e,W,hW,hxW,hyW,noZ⟩ := ih xR yR
   exact ⟨true::e,W,hW,hxW,hyW,noZ⟩

theorem original_subtree_two_X_contains_bottom {T V W : Tree} {X : List Nat}
 {e : RMAF.Vertex} {p q x y : Nat}
 (hn : (leaves T).Nodup) (hV : restrict X T = some V)
 (cat : Caterpillar V) (ch : HasCherry p q V) (hW : subtree T e = some W)
 (hx : x ∈ leaves W) (hy : y ∈ leaves W) (xX : x ∈ X) (yX : y ∈ X) (ne : x ≠ y) :
 p ∈ leaves W ∧ q ∈ leaves W := by
 have atW : BinaryExchange.treeAt T e = some W := by rw [source_treeAt]; exact hW
 have cl := BinaryExchange.cluster_restrict (BinaryExchange.subtree_cluster T W e hn atW) X (fun _ _ => trivial) hV
 have xT := (subtreeLabels_sublist T e).subset ((source_subtree_labels hW).symm ▸ hx)
 have yT := (subtreeLabels_sublist T e).subset ((source_subtree_labels hW).symm ▸ hy)
 have xV := (HardParent.restrict_mem hV x).2 ⟨xT,xX⟩
 have yV := (HardParent.restrict_mem hV y).2 ⟨yT,yX⟩
 have both := caterpillar_cluster_bottom cat ch cl xV yV ne (by simpa using hx) (by simpa using hy)
 exact ⟨List.contains_iff_mem.1 both.1,List.contains_iff_mem.1 both.2⟩

theorem subtree_contains_all_bottom_pendants {T W : Tree} {e r : RMAF.Vertex} {p q z : Nat}
 (hn : (leaves T).Nodup) (hW : subtree T e = some W)
 (hp : p ∈ leaves W) (hq : q ∈ leaves W)
 (hr : r ∈ cuts T p q) (hz : z ∈ subtreeLabels T r) : z ∈ leaves W := by
 have pE : p ∈ subtreeLabels T e := (source_subtree_labels hW).symm ▸ hp
 have qE : q ∈ subtreeLabels T e := (source_subtree_labels hW).symm ▸ hq
 have rs := (cuts_spec T p q r).1 hr
 have parent : r.dropLast ∈ minimalVertices (subtreeLabels T e) T :=
   executable_span_monotone T [p,q] _
     (by intro x hx; have hh : x = p ∨ x = q := by simpa using hx
         rcases hh with rfl | rfl <;> assumption) _ rs.2.2.1
 have ep := subtree_hull hn e r.dropLast parent
 obtain ⟨v,hv,rv⟩ := (subtreeLabels_prefix T r z).1 hz
 have zv : z ∈ subtreeLabels T e := (subtreeLabels_prefix T e z).2
   ⟨v,hv,ep.trans ((List.dropLast_prefix r).trans rv)⟩
 exact (source_subtree_labels hW) ▸ zv

/-- Original Case1 obstruction: an agreed component crossing a good source
pendant cannot contain two of its labels. The argument constructs a literal
target subtree, forces its bottom cherry into that subtree, and hence forces
the outside taxon into it, contradicting the source-induced rooted cluster. -/
theorem good_pendant_mixed_at_most_one {T S U V : Tree} {X : List Nat}
 {e : RMAF.Vertex} {p q : Nat} {F : List (List Nat)} {B : List Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (hU : subtree S e = some U) (hxU : leaves U = X)
 (hV : restrict X T = some V) (cat : Caterpillar V) (ch : HasCherry p q V)
 (outside : ∀ z, z ∈ leaves T → z ∉ X → ∃ r, r ∈ cuts T p q ∧ z ∈ subtreeLabels T r)
 (ha : agreement T S F = true) (hB : B ∈ F)
 {x y z : Nat} (xB : x ∈ B) (yB : y ∈ B) (zB : z ∈ B)
 (xX : x ∈ X) (yX : y ∈ X) (zX : z ∉ X) (ne : x ≠ y) : False := by
 have parts := BinaryExchange.agreement_parts T S F ha
 have atU : BinaryExchange.treeAt S e = some U := by rw [source_treeAt]; exact hU
 have cl := (BinaryExchange.descendant_agreed_split T S U e B hnS atU (parts.2.2.1 B hB)).1
 rw [hxU] at cl
 have xT := block_labels parts.1 hB xB
 have yT := block_labels parts.1 hB yB
 have zT := block_labels parts.1 hB zB
 obtain ⟨r,W,hW,xW,yW,noZ⟩ := cluster_actual_subtree cl xT yT xB yB zB
   (by simpa using xX) (by simpa using yX) (by simpa using zX)
 have pqW := original_subtree_two_X_contains_bottom hnT hV cat ch hW xW yW xX yX ne
 obtain ⟨s,hs,zs⟩ := outside z zT zX
 exact noZ (subtree_contains_all_bottom_pendants hnT hW pqW.1 pqW.2 hs zs)

theorem subtreeLabels_prefix_subset (T : Tree) {a b : RMAF.Vertex} (hp : a <+: b) :
 subtreeLabels T b ⊆ subtreeLabels T a := by
 intro x hx
 obtain ⟨v,hv,bv⟩ := (subtreeLabels_prefix T b x).1 hx
 exact (subtreeLabels_prefix T a x).2 ⟨v,hv,hp.trans bv⟩

theorem actual_pair_lca {T : Tree} {x y : Nat} (hx : x ∈ leaves T) (hy : y ∈ leaves T) :
 ∃ e W, subtree T e = some W ∧ x ∈ leaves W ∧ y ∈ leaves W ∧
 e ∈ minimalVertices [x,y] T := by
 obtain ⟨a,ha⟩ := leaf_exists hx
 obtain ⟨b,hb⟩ := leaf_exists hy
 have la : lca a b <+: a := path_root_prefix (lca_left_root a b)
 have lb : lca a b <+: b := path_root_prefix (lca_right_root a b)
 obtain ⟨W,hW⟩ := valid_ancestor ha.valid la
 refine ⟨lca a b,W,hW,?_,?_,?_⟩
 · exact (source_subtree_labels hW) ▸ ((subtreeLabels_prefix T (lca a b) x).2 ⟨a,ha,la⟩)
 · exact (source_subtree_labels hW) ▸ ((subtreeLabels_prefix T (lca a b) y).2 ⟨b,hb,lb⟩)
 · exact (minimalVertices_correct [x,y] T _).2
     ⟨a,b,(selected_at_leaf [x,y] T a x ha).2 (by simp),
       (selected_at_leaf [x,y] T b y hb).2 (by simp),lca_on_path a b⟩

/-- Root entry in the source and bottom entry in the target forbid every
other AF component from containing two X labels. The common restriction is
used only to transport a rooted cluster on the three original X labels. -/
theorem mixed_block_forbids_other_X_pair {T S U V : Tree} {X : List Nat}
 {e : RMAF.Vertex} {p q : Nat} {F : List (List Nat)} {B C : List Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (hU : subtree S e = some U) (hxU : leaves U = X)
 (hV : restrict X T = some V) (cat : Caterpillar V) (ch : HasCherry p q V)
 (good : restrictionAgrees T S X = true)
 (outside : ∀ z, z ∈ leaves T → z ∉ X → ∃ r, r ∈ cuts T p q ∧ z ∈ subtreeLabels T r)
 (ha : agreement T S F = true) (hB : B ∈ F) (hC : C ∈ F) (bc : B ≠ C)
 {x z u v : Nat} (xB : x ∈ B) (zB : z ∈ B) (xX : x ∈ X) (zX : z ∉ X)
 (uC : u ∈ C) (vC : v ∈ C) (uX : u ∈ X) (vX : v ∈ X) (uv : u ≠ v) : False := by
 have parts := BinaryExchange.agreement_parts T S F ha
 have sourceChecks := source_agreement_checks ha
 have targetEmb := (executable_pairwiseEmbeddings T F).2 parts.2.2.2.1
 have uS := block_labels parts.2.1 hC uC
 have vS := block_labels parts.2.1 hC vC
 have xS := block_labels parts.2.1 hB xB
 have zS := block_labels parts.2.1 hB zB
 have uT := block_labels parts.1 hC uC
 have vT := block_labels parts.1 hC vC
 have zT := block_labels parts.1 hB zB
 obtain ⟨w,W,hW,uW,vW,wuv⟩ := actual_pair_lca uS vS
 have eW : e <+: w := by
   have labs : subtreeLabels S e = X := (source_subtree_labels hU).trans hxU
   have wh : w ∈ minimalVertices (subtreeLabels S e) S := executable_span_monotone S [u,v] _
     (by intro t ht; have hh : t = u ∨ t = v := by simpa using ht
         rw [labs]; rcases hh with rfl | rfl <;> assumption) w wuv
   exact subtree_hull hnS e w wh
 have Wsub : leaves W ⊆ X := by
   rw [←hxU,←source_subtree_labels hU,←source_subtree_labels hW]
   exact subtreeLabels_prefix_subset S eW
 have zW : z ∉ leaves W := fun hz => zX (Wsub hz)
 have wC : w ∈ minimalVertices C S := executable_span_monotone S [u,v] C
   (by intro t ht; have hh : t = u ∨ t = v := by simpa using ht
       rcases hh with rfl | rfl <;> assumption) w wuv
 have xW : x ∉ leaves W := by
   intro xw
   have atW : BinaryExchange.treeAt S w = some W := by rw [source_treeAt]; exact hW
   have wB := BinaryExchange.crossing_occupies S W w B hnS atW
     (fun t ht => block_labels parts.2.1 hB ht) ⟨⟨x,xB,xw⟩,⟨z,zB,zW⟩⟩
   exact bc (checked_support_unique S F sourceChecks.2 B C hB hC w wB wC)
 have tri : restrictionAgrees T S [u,v,x] = true := BinaryExchange.restrictionAgrees_sub T S X [u,v,x] good
   (by intro t ht; have hh : t = u ∨ t = v ∨ t = x := by simpa using ht
       rcases hh with rfl | rfl | rfl <;> assumption) ⟨u,by simp,uT⟩
 have atW : BinaryExchange.treeAt S w = some W := by rw [source_treeAt]; exact hW
 have cl := (BinaryExchange.descendant_agreed_split T S W w [u,v,x] hnS atW tri).1
 obtain ⟨r,R,hR,uR,vR,xR⟩ := cluster_actual_subtree (x:=u) (y:=v) (z:=x) cl uT vT (by simp) (by simp) (by simp)
   (by simpa using uW) (by simpa using vW) (by simpa using xW)
 obtain ⟨g,G,hG,uG,vG,guv⟩ := actual_pair_lca uT vT
 have rg : r <+: g := by
   have uh : u ∈ subtreeLabels T r := (source_subtree_labels hR).symm ▸ uR
   have vh : v ∈ subtreeLabels T r := (source_subtree_labels hR).symm ▸ vR
   exact subtree_hull hnT r g (executable_span_monotone T [u,v] _
     (by intro t ht; have hh : t = u ∨ t = v := by simpa using ht
         rcases hh with rfl | rfl <;> assumption) g guv)
 have xG : x ∉ leaves G := by
   intro xg
   have sub := subtreeLabels_prefix_subset T rg ((source_subtree_labels hG).symm ▸ xg)
   exact xR ((source_subtree_labels hR) ▸ sub)
 have pqG := original_subtree_two_X_contains_bottom hnT hV cat ch hG uG vG uX vX uv
 obtain ⟨s,hs,zs⟩ := outside z zT zX
 have zG := subtree_contains_all_bottom_pendants hnT hG pqG.1 pqG.2 hs zs
 have atG : BinaryExchange.treeAt T g = some G := by rw [source_treeAt]; exact hG
 have gB := BinaryExchange.crossing_occupies T G g B hnT atG
   (fun t ht => block_labels parts.1 hB ht) ⟨⟨z,zB,zG⟩,⟨x,xB,xG⟩⟩
 have gC := executable_span_monotone T [u,v] C
   (by intro t ht; have hh : t = u ∨ t = v := by simpa using ht
       rcases hh with rfl | rfl <;> assumption) g guv
 exact bc (checked_support_unique T F targetEmb B C hB hC g gB gC)

end Universal233.Rule5Classification
