import Rule5Exchange
namespace Universal233.Rule5Local
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching

theorem original_fork_occupies {T L R : Tree} {q : RMAF.Vertex}
 {B : List Nat} {x y : Nat} (he : subtree T q = some (.node L R))
 (hx : x ∈ leaves L) (hy : y ∈ leaves R) (xB : x ∈ B) (yB : y ∈ B) :
 q ∈ minimalVertices B T := by
 obtain ⟨u,hu⟩ := leaf_exists hx
 obtain ⟨v,hv⟩ := leaf_exists hy
 have hux : LeafAt T (q ++ (false::u)) x := by
   unfold LeafAt
   rw [subtree_append he]
   exact hu
 have hvy : LeafAt T (q ++ (true::v)) y := by
   unfold LeafAt
   rw [subtree_append he]
   exact hv
 apply (minimalVertices_correct B T q).2
 refine ⟨q ++ (false::u),q ++ (true::v),(selected_at_leaf B T _ x hux).2 xB,
   (selected_at_leaf B T _ y hvy).2 yB,?_⟩
 simpa using path_prepend q (PathAt.fork u v)

theorem singleton_excludes_other {S : Tree} {F : List (List Nat)} {a x : Nat}
 {B : List Nat} (hp : partitionCheck (leaves S) F = true)
 (ha : [a] ∈ F) (hB : B ∈ F) (hx : x ∈ B) (hxa : x ≠ a) : a ∉ B := by
 intro hm
 have e := ForestState.checked_unique_block (leaves S) F hp B [a] hB ha a hm (by simp)
 have ex : x = a := by simpa [e] using hx
 exact hxa ex

/-- Every X-crossing block, when a is singleton, occupies the actual source
vertex immediately above the a/X sibling pair and c. -/
theorem source_mixedX_occupies {S X : Tree} {v : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a c : Nat}
 (hn : (leaves S).Nodup)
 (he : subtree S v = some (.node (.node (.leaf a) X) (.leaf c)))
 (xa : a ∉ leaves X) (xc : c ∉ leaves X)
 (hp : partitionCheck (leaves S) F = true) (single : [a] ∈ F) (hB : B ∈ F)
 (hm : BinaryExchange.mixed B (leaves X).contains = true) :
 v ∈ minimalVertices B S := by
 obtain ⟨⟨x,xB,xX⟩,⟨y,yB,yX⟩⟩ := (BinaryExchange.mixed_iff B _).1 hm
 have xX' : x ∈ leaves X := List.contains_iff_mem.1 xX
 have yX' : y ∉ leaves X := by simpa using yX
 have xna : x ≠ a := by intro e; subst x; exact xa xX'
 have noA := singleton_excludes_other hp single hB xB xna
 have yna : y ≠ a := by intro e; subst y; exact noA yB
 by_cases yc : y = c
 · subst y
   exact original_fork_occupies he (by simp [leaves,xX']) (by simp [leaves]) xB yB
 · have yo : y ∉ leaves (.node (.node (.leaf a) X) (.leaf c)) := by
     simp [leaves,yna,yX',yc]
   have xi : x ∈ leaves (.node (.node (.leaf a) X) (.leaf c)) := by simp [leaves,xX']
   have atV : BinaryExchange.treeAt S v = some (.node (.node (.leaf a) X) (.leaf c)) := by
     rw [source_treeAt]; exact he
   exact BinaryExchange.crossing_occupies S _ v B hn atV (fun z hz => block_labels hp hB hz)
     ⟨⟨x,xB,xi⟩,⟨y,yB,yo⟩⟩

theorem source_cmixed_noX_occupies {S X : Tree} {v : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a c : Nat}
 (hn : (leaves S).Nodup)
 (he : subtree S v = some (.node (.node (.leaf a) X) (.leaf c)))
 (hac : a ≠ c)
 (hp : partitionCheck (leaves S) F = true) (single : [a] ∈ F) (hB : B ∈ F)
 (cB : c ∈ B) (noX : ∀ x, x ∈ B → x ∉ leaves X)
 (other : ∃ y, y ∈ B ∧ y ≠ c) : v ∈ minimalVertices B S := by
 obtain ⟨y,yB,ync⟩ := other
 have noA := singleton_excludes_other hp single hB cB (Ne.symm hac)
 have yna : y ≠ a := by intro e; subst y; exact noA yB
 have yo : y ∉ leaves (.node (.node (.leaf a) X) (.leaf c)) := by
   simp [leaves,yna,noX y yB,ync]
 have ci : c ∈ leaves (.node (.node (.leaf a) X) (.leaf c)) := by simp [leaves]
 have atV : BinaryExchange.treeAt S v = some (.node (.node (.leaf a) X) (.leaf c)) := by
   rw [source_treeAt]; exact he
 exact BinaryExchange.crossing_occupies S _ v B hn atV (fun z hz => block_labels hp hB hz)
   ⟨⟨c,cB,ci⟩,⟨y,yB,yo⟩⟩

/-- A three-part crossing in Figure15.3 is prohibited by actual original
cluster laminarity. This covers any C taxon, including every S rung. -/
theorem case323_no_three_part_block {S X U : Tree} {v : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a c x d : Nat}
 (hnT : (leaves (.node (.leaf c) U)).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S v = some (.node (.node (.leaf a) X) (.leaf c)))
 (xc : c ∉ leaves X) (xX : x ∈ leaves X)
 (da : d ≠ a) (dc : d ≠ c) (dX : d ∉ leaves X)
 (ha : agreement (.node (.leaf c) U) S F = true) (hB : B ∈ F)
 (xB : x ∈ B) (cB : c ∈ B) (dB : d ∈ B) : False := by
 have hpT := (BinaryExchange.agreement_parts (.node (.leaf c) U) S F ha).1
 have xT := block_labels hpT hB xB
 have dT := block_labels hpT hB dB
 have xnc : x ≠ c := by intro e; subst x; exact xc xX
 have xU : x ∈ leaves U := by simpa [leaves,xnc] using xT
 have dU : d ∈ leaves U := by simpa [leaves,dc] using dT
 have cnU : c ∉ leaves U := by
   have ht : (c :: leaves U).Nodup := by simpa [leaves] using hnT
   exact (List.nodup_cons.1 ht).1
 have xnV : x ∈ leaves (.node (.node (.leaf a) X) (.leaf c)) := by simp [leaves,xX]
 have dnV : d ∉ leaves (.node (.node (.leaf a) X) (.leaf c)) := by simp [leaves,da,dc,dX]
 have cnV : c ∈ leaves (.node (.node (.leaf a) X) (.leaf c)) := by simp [leaves]
 exact original_crossing_clusters_exclude_block hnT hnS (q:=[true]) rfl he
   xU dU cnU xnV dnV cnV ha hB xB dB cB

theorem source_base_proper {S X : Tree} {v : RMAF.Vertex} {a c : Nat}
 (hn : (leaves S).Nodup)
 (he : subtree S v = some (.node (.node (.leaf a) X) (.leaf c))) :
 a ∉ leaves X ∧ c ∉ leaves X ∧ a ≠ c := by
 have nd := (subtreeLabels_sublist S v).nodup hn
 rw [source_subtree_labels he] at nd
 have nd' : (a :: (leaves X ++ [c])).Nodup := by simpa [leaves] using nd
 have ap := (List.nodup_cons.1 nd').1
 have tail := (List.nodup_cons.1 nd').2
 have cross := (List.nodup_append.1 tail).2.2
 refine ⟨fun h => ap (by simp [h]),?_,?_⟩
 · intro h; exact cross c h c (by simp) rfl
 · intro e; subst c; exact ap (by simp)

/-- Literal Figure15.3 split saving, derived from source occupancy and
original crossing-cluster exclusion. This is the graph/count step consumed
by the no-larger exchange, not an assumed saving field. -/
theorem case323_split_saving {S X U : Tree} {v : RMAF.Vertex}
 {F : List (List Nat)} {a c : Nat}
 (hnT : (leaves (.node (.leaf c) U)).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S v = some (.node (.node (.leaf a) X) (.leaf c)))
 (ha : agreement (.node (.leaf c) U) S F = true) (single : [a] ∈ F) :
 (splitForest (splitForest F (leaves X)) [c]).length ≤ F.length+1 := by
 obtain ⟨xa,xc,hac⟩ := source_base_proper hnS he
 have parts := BinaryExchange.agreement_parts (.node (.leaf c) U) S F ha
 have hp := parts.2.1
 have emb := parts.2.2.2.2
 have hq : subtree S (v ++ [false,true]) = some X := by
   rw [subtree_append he]; rfl
 have hr : subtree S (v ++ [true]) = some (.leaf c) := by
   rw [subtree_append he]; rfl
 have first := split_original_agreement hnS hq ha
 let H := splitForest F (leaves X)
 change (splitForest H [c]).length ≤ F.length+1
 change agreement (.node (.leaf c) U) S H = true ∧ H.length ≤ F.length+1 at first
 have second := split_original_agreement hnS hr first.1
 change agreement (.node (.leaf c) U) S (splitForest H [c]) = true ∧
   (splitForest H [c]).length ≤ H.length+1 at second
 by_cases hasMixed : ∃ C, C ∈ H ∧ BinaryExchange.mixed C [c].contains = true
 · obtain ⟨C,hC,hmC⟩ := hasMixed
   obtain ⟨D,hD,hDC⟩ := List.mem_flatMap.1 hC
   have sub := BinaryExchange.split_sub D C (leaves X).contains hDC
   obtain ⟨⟨z,zC,zc⟩,⟨d,dC,dc⟩⟩ := (BinaryExchange.mixed_iff C [c].contains).1 hmC
   have z_eq : z = c := by simpa using zc
   subst z
   have dnc : d ≠ c := by simpa using dc
   have cD := sub c zC
   have dD := sub d dC
   have noA := singleton_excludes_other hp single hD cD (Ne.symm hac)
   have dna : d ≠ a := by intro e; subst d; exact noA dD
   have CnoX : ∀ y, y ∈ C → y ∉ leaves X := by
     rcases BinaryExchange.split_mono D (leaves X).contains C hDC with hy | hn
     · exact False.elim (xc (List.contains_iff_mem.1 (hy c zC)))
     · intro y hy; have hh := hn y hy; simpa using hh
   have DnoX : ∀ y, y ∈ D → y ∉ leaves X := by
     intro y yD yX
     exact case323_no_three_part_block hnT hnS he xc yX dna dnc (CnoX d dC)
       ha hD yD cD dD
   have occD := source_cmixed_noX_occupies hnS he hac hp single hD cD DnoX ⟨d,dD,dnc⟩
   have noFirst : ∀ B, B ∈ F → BinaryExchange.mixed B (leaves X).contains = false := by
     intro B hB
     apply Bool.eq_false_iff.2
     intro mixedB
     have occB := source_mixedX_occupies hnS he xa xc hp single hB mixedB
     have neBD : B ≠ D := by
       intro e
       obtain ⟨⟨y,yB,yX⟩,_⟩ := (BinaryExchange.mixed_iff B (leaves X).contains).1 mixedB
       exact DnoX y (e ▸ yB) (List.contains_iff_mem.1 yX)
     have dj := BinaryExchange.pairwise_mem (fun _ _ h => BinaryExchange.disj_symm h)
       F emb B D hB hD neBD
     exact dj v ⟨(minimalVertices_correct B S v).1 occB,(minimalVertices_correct D S v).1 occD⟩
   have empty : F.filter (fun B => BinaryExchange.mixed B (leaves X).contains) = [] := by
     apply List.filter_eq_nil_iff.2
     intro B hB hm
     rw [noFirst B hB] at hm
     contradiction
   have len := BinaryExchange.splitAll_length F (leaves X).contains
   rw [empty] at len
   have Hlen : H.length ≤ F.length := by simpa [H,splitForest] using len
   omega
 · have empty : H.filter (fun C => BinaryExchange.mixed C [c].contains) = [] := by
     apply List.filter_eq_nil_iff.2
     intro C hC
     exact fun hm => hasMixed ⟨C,hC,hm⟩
   have len := BinaryExchange.splitAll_length H [c].contains
   rw [empty] at len
   have endlen : (splitForest H [c]).length ≤ H.length := by simpa [splitForest] using len
   omega

/-- Actual no-larger original Figure15.3 exchange in the displayed source
orientation. Source classification and the remaining orientations are stated
as open consumers in FIRST-GAP-v1.md; no coverage field is imported here. -/
theorem actual_case323_exchange {S X U : Tree} {v p : RMAF.Vertex}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves (.node (.leaf c) U)).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves (.node (.leaf c) U) ↔ x ∈ leaves S)
 (he : subtree S v = some (.node (.node (.leaf a) X) (.leaf c)))
 (ch : CherryAt (.node (.leaf c) U) p a b)
 (hc : cuts S a b = [v ++ [false,true],v ++ [true]])
 (ha : agreement (.node (.leaf c) U) S F = true) :
 [b] ∈ F ∨ ∃ G, agreement (.node (.leaf c) U) S G = true ∧
 G.length ≤ F.length ∧ VertexGeometry.Refines G (pendantPartition S a b) := by
 rcases actual_pendant_safety hnS ha ch with single | single | ref
 · right
   apply actual_hard2_exchange_from_split_saving hnT hnS same ha ch hc single
   have hq : subtree S (v ++ [false,true]) = some X := by rw [subtree_append he]; rfl
   have hr : subtree S (v ++ [true]) = some (.leaf c) := by rw [subtree_append he]; rfl
   rw [splitTwo,source_subtree_labels hq,source_subtree_labels hr]
   exact case323_split_saving hnT hnS he ha single
 · exact Or.inl single
 · exact Or.inr ⟨F,ha,Nat.le_refl _,ref⟩

end Universal233.Rule5Local
