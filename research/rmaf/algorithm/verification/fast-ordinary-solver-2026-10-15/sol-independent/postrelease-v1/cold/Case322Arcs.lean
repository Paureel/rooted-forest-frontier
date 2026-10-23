import Case322Saving
namespace Universal233.Rule5Case322
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local
set_option maxRecDepth 10000

/-- Original edge crossing occupies its parent as well as its child. -/
theorem mixed_original_parent {T U : Tree} {q : RMAF.Vertex} {F : List (List Nat)} {D : List Nat}
 (hn : (leaves T).Nodup) (hq : subtree T q = some U) (nonroot : q ≠ [])
 (hp : partitionCheck (leaves T) F = true) (hD : D ∈ F)
 (mixed : BinaryExchange.mixed D (leaves U).contains = true) : q.dropLast ∈ minimalVertices D T := by
 rcases List.eq_nil_or_concat q with h | ⟨p,s,h⟩
 · exact False.elim (nonroot h)
 have eq : q = p ++ [s] := by simpa only [List.concat_eq_append] using h
 have validp := valid_ancestor (show Valid T q from ⟨U,hq⟩) (by rw [eq]; exact List.prefix_append _ _)
 obtain ⟨P,hP⟩ := validp
 cases P with
 | leaf z =>
   rw [eq,subtree_append hP] at hq
   simp [subtree] at hq
 | node L R =>
   obtain ⟨⟨x,xD,xU⟩,⟨y,yD,yU⟩⟩ := (BinaryExchange.mixed_iff D (leaves U).contains).1 mixed
   have xi : x ∈ leaves U := List.contains_iff_mem.1 xU
   have yo : y ∉ leaves U := by simpa using yU
   have child : (if s then R else L) = U := by
     rw [eq,subtree_append hP] at hq
     simpa [subtree] using hq
   have xP : x ∈ leaves (.node L R) := by cases s <;> simp_all [leaves]
   have occ : p ∈ minimalVertices D T := by
     by_cases yp : y ∈ leaves (.node L R)
     · cases s
       · have xu : x ∈ leaves L := by rw [show L = U from child]; exact xi
         have yl : y ∉ leaves L := by rw [show L = U from child]; exact yo
         have yr : y ∈ leaves R := (List.mem_append.1 yp).resolve_left yl
         exact original_fork_occupies hP xu yr xD yD
       · have xu : x ∈ leaves R := by rw [show R = U from child]; exact xi
         have yr : y ∉ leaves R := by rw [show R = U from child]; exact yo
         have yl : y ∈ leaves L := (List.mem_append.1 yp).resolve_right yr
         exact original_fork_occupies hP yl xu yD xD
     · have atP : BinaryExchange.treeAt T p = some (.node L R) := by rw [source_treeAt]; exact hP
       exact BinaryExchange.crossing_occupies T _ p D hn atP (fun z hz => block_labels hp hD hz)
         ⟨⟨x,xD,xP⟩,⟨y,yD,yp⟩⟩
   simpa [eq] using occ

/-- An actual b--c path pendant arc is unused by every original AF block
when its labels are absent from the b,c anchor block. Both child orientations
are included by the literal original-edge definition of cuts. -/
theorem anchor_unused_pendant {T S U : Tree} {q : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {b c : Nat}
 (hnT : (leaves T).Nodup) (ha : agreement T S F = true)
 (hq : q ∈ cuts T b c) (lookup : subtree T q = some U)
 (hB : B ∈ F) (bB : b ∈ B) (cB : c ∈ B)
 (noU : ∀ x, x ∈ B → x ∉ leaves U) :
 ∀ D, D ∈ F → BinaryExchange.mixed D (leaves U).contains ≠ true := by
 intro D hD hm
 have parts := BinaryExchange.agreement_parts T S F ha
 have spec := (cuts_spec T b c q).1 hq
 have occB : q.dropLast ∈ minimalVertices B T := by
   apply (minimalVertices_correct B T _).2
   apply BinaryExchange.hull_mono T [b,c] B
   · intro x hx; have e : x = b ∨ x = c := by simpa using hx
     rcases e with rfl | rfl <;> assumption
   · exact (minimalVertices_correct [b,c] T _).1 spec.2.2.1
 have occD := mixed_original_parent hnT lookup spec.2.1 parts.1 hD hm
 have ne : D ≠ B := by
   intro e
   obtain ⟨⟨x,xD,xU⟩,_⟩ := (BinaryExchange.mixed_iff D (leaves U).contains).1 hm
   exact noU x (e ▸ xD) (List.contains_iff_mem.1 xU)
 have dj := BinaryExchange.pairwise_mem (fun _ _ h => BinaryExchange.disj_symm h) F parts.2.2.2.1 D B hD hB ne
 exact dj q.dropLast ⟨(minimalVertices_correct D T _).1 occD,(minimalVertices_correct B T _).1 occB⟩

/-- Type3(ii): a literal b-side original subtree cannot be used by the b,c
anchor block. The exclusion is obtained from actual incompatible target and
source clusters, not from an asserted unused-edge or cover field. -/
theorem bside_anchor_excludes {T S X U W : Tree} {w q r : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (lookup : subtree T q = some U) (upper : subtree T r = some W)
 (uX : ∀ x, x ∈ leaves U → x ∈ leaves X)
 (uW : ∀ x, x ∈ leaves U → x ∈ leaves W) (bW : b ∈ leaves W) (cW : c ∉ leaves W)
 (ha : agreement T S F = true) (hB : B ∈ F) (bB : b ∈ B) (cB : c ∈ B) :
 ∀ x, x ∈ B → x ∉ leaves U := by
 have base : subtree S (w ++ [false]) = some (.node (.node (.leaf a) X) (.leaf c)) := by rw [subtree_append he]; rfl
 have bV : b ∉ leaves (.node (.node (.leaf a) X) (.leaf c)) := by
   have nd := (subtreeLabels_sublist S w).nodup hnS
   rw [source_subtree_labels he] at nd
   have cross := (List.nodup_append.1 nd).2.2
   exact fun h => cross b h b (by simp [leaves]) rfl
 intro x xB xU
 exact original_crossing_clusters_exclude_block hnT hnS upper base
   (uW x xU) bW cW (by simp [leaves,uX x xU]) bV (by simp [leaves]) ha hB xB bB cB

/-- The whole type3(ii) list of b-side arcs is individually unused. There is
no union-of-suppressed-cuts argument and no implicit payment discount. -/
theorem bside_original_unused {T S X U W : Tree} {w q r : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (hq : q ∈ cuts T b c) (lookup : subtree T q = some U) (upper : subtree T r = some W)
 (uX : ∀ x, x ∈ leaves U → x ∈ leaves X)
 (uW : ∀ x, x ∈ leaves U → x ∈ leaves W) (bW : b ∈ leaves W) (cW : c ∉ leaves W)
 (ha : agreement T S F = true) (hB : B ∈ F) (bB : b ∈ B) (cB : c ∈ B) :
 ∀ D, D ∈ F → BinaryExchange.mixed D (leaves U).contains ≠ true :=
 anchor_unused_pendant hnT ha hq lookup hB bB cB
   (bside_anchor_excludes hnT hnS he lookup upper uX uW bW cW ha hB bB cB)

/-- Type3(i): among two actual c-side original pendants in path order, at
least one has no anchor label. Two used arcs would make incompatible actual
clusters (the source X cluster and the lower target c-side cluster). -/
theorem cside_two_anchor_alternative {T S X U V W : Tree} {w q r z : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (lookupU : subtree T q = some U) (lookupV : subtree T r = some V)
 (lower : subtree T z = some W) (cW : c ∈ leaves W)
 (uW : ∀ x, x ∈ leaves U → x ∈ leaves W) (vW : ∀ y, y ∈ leaves V → y ∉ leaves W)
 (uX : ∀ x, x ∈ leaves U → x ∈ leaves X) (vX : ∀ y, y ∈ leaves V → y ∈ leaves X)
 (ha : agreement T S F = true) (hB : B ∈ F) (cB : c ∈ B) :
 (∀ x, x ∈ B → x ∉ leaves U) ∨ (∀ y, y ∈ B → y ∉ leaves V) := by
 have sourceX : subtree S (w ++ [false,false,true]) = some X := by rw [subtree_append he]; rfl
 have base : subtree S (w ++ [false]) = some (.node (.node (.leaf a) X) (.leaf c)) := by rw [subtree_append he]; rfl
 have xc := (source_base_proper hnS base).2.1
 by_cases noU : ∀ x, x ∈ B → x ∉ leaves U
 · exact Or.inl noU
 · right
   intro y yB yV
   apply noU
   intro x xB xU
   exact original_crossing_clusters_exclude_block hnT hnS lower sourceX
     (uW x xU) cW (vW y yV) (uX x xU) xc (vX y yV) ha hB xB cB yB

/-- The literal selected pair in type3(i) has an entirely unused original
arc. This is a two-element LIST alternative; neither duplicate removal nor a
max/union bound is used. -/
theorem cside_two_original_unused {T S X U V W : Tree} {w q r z : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (qcut : q ∈ cuts T b c) (rcut : r ∈ cuts T b c)
 (lookupU : subtree T q = some U) (lookupV : subtree T r = some V)
 (lower : subtree T z = some W) (cW : c ∈ leaves W)
 (uW : ∀ x, x ∈ leaves U → x ∈ leaves W) (vW : ∀ y, y ∈ leaves V → y ∉ leaves W)
 (uX : ∀ x, x ∈ leaves U → x ∈ leaves X) (vX : ∀ y, y ∈ leaves V → y ∈ leaves X)
 (ha : agreement T S F = true) (hB : B ∈ F) (bB : b ∈ B) (cB : c ∈ B) :
 (∀ D, D ∈ F → BinaryExchange.mixed D (leaves U).contains ≠ true) ∨
 (∀ D, D ∈ F → BinaryExchange.mixed D (leaves V).contains ≠ true) := by
 rcases cside_two_anchor_alternative hnT hnS he lookupU lookupV lower cW uW vW uX vX ha hB cB with noU | noV
 · exact Or.inl (anchor_unused_pendant hnT ha qcut lookupU hB bB cB noU)
 · exact Or.inr (anchor_unused_pendant hnT ha rcut lookupV hB bB cB noV)

/-- Type3(iii): the anchor block lies below the actual b,c ancestor cut.
Actual core and source clusters exclude any extra label outside that cut. -/
theorem ancestor_anchor_contained {T S X W C : Tree} {w q r : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (lookup : subtree T q = some W) (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bW : b ∈ leaves W) (cW : c ∈ leaves W) (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (ha : agreement T S F = true) (single : [a] ∈ F) (hB : B ∈ F) (bB : b ∈ B) (cB : c ∈ B)
 (hab : a ≠ b) : ∀ x, x ∈ B → x ∈ leaves W := by
 have base : subtree S (w ++ [false]) = some (.node (.node (.leaf a) X) (.leaf c)) := by rw [subtree_append he]; rfl
 have bV : b ∉ leaves (.node (.node (.leaf a) X) (.leaf c)) := by
   have nd := (subtreeLabels_sublist S w).nodup hnS
   rw [source_subtree_labels he] at nd
   have cross := (List.nodup_append.1 nd).2.2
   exact fun h => cross b h b (by simp [leaves]) rfl
 have parts := BinaryExchange.agreement_parts T S F ha
 have noA := singleton_excludes_other parts.1 single hB bB (Ne.symm hab)
 intro x xB
 apply Classical.byContradiction
 intro noW
 by_cases xX : x ∈ leaves X
 · exact original_crossing_clusters_exclude_block hnT hnS lookup base cW bW noW
     (by simp [leaves]) bV (by simp [leaves,xX]) ha hB cB bB xB
 · have xnc : x ≠ c := by intro e; subst x; exact noW cW
   have xnb : x ≠ b := by intro e; subst x; exact noW bW
   have xna : x ≠ a := by intro e; subst x; exact noA xB
   have xC := (coreLabels x (block_labels parts.1 hB xB)).2 ⟨xX,xnc⟩
   have xSource : x ∉ leaves (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)) := by
     simp [leaves,xna,xX,xnc,xnb]
   exact original_crossing_clusters_exclude_block hnT hnS core he bC xC cC
     (by simp [leaves]) xSource (by simp [leaves]) ha hB bB xB cB

/-- The entering ancestor arc in type3(iii) is unused by every AF block;
its child endpoint is occupied by the b,c anchor, excluding other crossings. -/
theorem ancestor_original_unused {T S X W C : Tree} {w q r : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (lookup : subtree T q = some W) (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bW : b ∈ leaves W) (cW : c ∈ leaves W) (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (onPath : q ∈ minimalVertices [b,c] T)
 (ha : agreement T S F = true) (single : [a] ∈ F) (hB : B ∈ F) (bB : b ∈ B) (cB : c ∈ B)
 (hab : a ≠ b) : ∀ D, D ∈ F → BinaryExchange.mixed D (leaves W).contains ≠ true := by
 have allB := ancestor_anchor_contained hnT hnS he lookup core coreLabels bW cW bC cC ha single hB bB cB hab
 have parts := BinaryExchange.agreement_parts T S F ha
 have occB : q ∈ minimalVertices B T := by
   apply (minimalVertices_correct B T q).2
   apply BinaryExchange.hull_mono T [b,c] B
   · intro x hx; have e : x = b ∨ x = c := by simpa using hx
     rcases e with rfl | rfl <;> assumption
   · exact (minimalVertices_correct [b,c] T q).1 onPath
 intro D hD mixed
 obtain ⟨_,⟨y,yD,yW⟩⟩ := (BinaryExchange.mixed_iff D (leaves W).contains).1 mixed
 have yn : y ∉ leaves W := by simpa using yW
 have ne : D ≠ B := by intro e; exact yn (allB y (e ▸ yD))
 have atQ : BinaryExchange.treeAt T q = some W := by rw [source_treeAt]; exact lookup
 have occD := BinaryExchange.crossing_occupies T W q D hnT atQ (fun z hz => block_labels parts.1 hD hz)
   (by obtain ⟨⟨x,xD,xW⟩,_⟩ := (BinaryExchange.mixed_iff D (leaves W).contains).1 mixed
       exact ⟨⟨x,xD,List.contains_iff_mem.1 xW⟩,⟨y,yD,yn⟩⟩)
 have dj := BinaryExchange.pairwise_mem (fun _ _ h => BinaryExchange.disj_symm h) F parts.2.2.2.1 D B hD hB ne
 exact dj q ⟨(minimalVertices_correct D T q).1 occD,(minimalVertices_correct B T q).1 occB⟩
end Universal233.Rule5Case322
