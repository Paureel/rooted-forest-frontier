import Rule5Case323
namespace Universal233.Rule5Local
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching

theorem nonsingleton_block_parent {S : Tree} {q : RMAF.Vertex} {side : Bool}
 {a : Nat} {F : List (List Nat)} {B : List Nat}
 (hl : LeafAt S (q ++ [side]) a)
 (hp : partitionCheck (leaves S) F = true) (hB : B ∈ F) (aB : a ∈ B)
 (nonsingle : [a] ∉ F) : q ∈ minimalVertices B S := by
 have other : ∃ x, x ∈ B ∧ x ≠ a := by
   apply Classical.byContradiction
   intro no
   have only : ∀ x, x ∈ B → x = a := by
     intro x hx
     by_cases h : x = a
     · exact h
     · exact False.elim (no ⟨x,hx,h⟩)
   have e := block_singleton_of_only hp hB aB only
   exact nonsingle (e ▸ hB)
 obtain ⟨x,xB,xna⟩ := other
 obtain ⟨w,hw⟩ := leaf_exists (block_labels hp hB xB)
 have aSpan := (minimalVertices_terminal B S (q ++ [side]) a hl).2 aB
 have xSpan := (minimalVertices_terminal B S w x hw).2 xB
 have ne : w ≠ q ++ [side] := by
   intro e
   rw [e] at hw
   unfold LeafAt at hl hw
   have eq : x = a := Tree.leaf.inj (Option.some.inj (hw.symm.trans hl))
   exact xna eq
 exact walk_from_leaf_visits_parent hl (minimalVertices_connected B S _ _ aSpan xSpan) ne

/-- When source a is the literal sibling of X and is non-singleton, every
X-crossing final block contains a. This follows from original parent occupancy. -/
theorem mixedX_contains_nonsingleton_sibling {S X : Tree} {q : RMAF.Vertex}
 {F : List (List Nat)} {B : List Nat} {a : Nat}
 (hn : (leaves S).Nodup) (he : subtree S q = some (.node (.leaf a) X))
 (hp : partitionCheck (leaves S) F = true) (emb : F.Pairwise (BinaryExchange.Disj S))
 (nonsingle : [a] ∉ F) (hB : B ∈ F)
 (hm : BinaryExchange.mixed B (leaves X).contains = true) : a ∈ B := by
 apply Classical.byContradiction
 intro noA
 have leafA : LeafAt S (q ++ [false]) a := by rw [LeafAt,subtree_append he]; rfl
 obtain ⟨A,hA,aA⟩ := partitionCheck_covers (leaves S) F hp a (leafAt_label S _ a leafA)
 have occA := nonsingleton_block_parent leafA hp hA aA nonsingle
 obtain ⟨⟨x,xB,xX⟩,⟨y,yB,yX⟩⟩ := (BinaryExchange.mixed_iff B _).1 hm
 have xX' : x ∈ leaves X := List.contains_iff_mem.1 xX
 have yX' : y ∉ leaves X := by simpa using yX
 have yna : y ≠ a := by intro e; subst y; exact noA yB
 have yo : y ∉ leaves (.node (.leaf a) X) := by simp [leaves,yna,yX']
 have xi : x ∈ leaves (.node (.leaf a) X) := by simp [leaves,xX']
 have atQ : BinaryExchange.treeAt S q = some (.node (.leaf a) X) := by rw [source_treeAt]; exact he
 have occB := BinaryExchange.crossing_occupies S _ q B hn atQ (fun z hz => block_labels hp hB hz)
   ⟨⟨x,xB,xi⟩,⟨y,yB,yo⟩⟩
 have neBA : B ≠ A := by intro e; exact noA (e ▸ aA)
 have dj := BinaryExchange.pairwise_mem (fun _ _ h => BinaryExchange.disj_symm h) F emb B A hB hA neBA
 exact dj q ⟨(minimalVertices_correct B S q).1 occB,(minimalVertices_correct A S q).1 occA⟩

theorem case321_split_saving {T S X W : Tree} {v w : RMAF.Vertex}
 {F : List (List Nat)} {a c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (he : subtree S v = some (.node (.node (.leaf a) X) (.leaf c)))
 (hw : subtree T w = some W)
 (Wlabels : ∀ x, x ∈ leaves W ↔ x ∈ leaves X ∨ x = c)
 (ha : agreement T S F = true) (nonsingle : [a] ∉ F) :
 (splitForest (splitForest F (leaves X)) [c]).length ≤ F.length+1 := by
 obtain ⟨xa,xc,hac⟩ := source_base_proper hnS he
 have parts := BinaryExchange.agreement_parts T S F ha
 have hp := parts.2.1
 have embT := parts.2.2.2.1
 have embS := parts.2.2.2.2
 have sibling : subtree S (v ++ [false]) = some (.node (.leaf a) X) := by rw [subtree_append he]; rfl
 have hq : subtree S (v ++ [false,true]) = some X := by rw [subtree_append he]; rfl
 have hr : subtree S (v ++ [true]) = some (.leaf c) := by rw [subtree_append he]; rfl
 have first := split_original_agreement hnS hq ha
 let H := splitForest F (leaves X)
 change (splitForest H [c]).length ≤ F.length+1
 change agreement T S H = true ∧ H.length ≤ F.length+1 at first
 have second := split_original_agreement hnS hr first.1
 change agreement T S (splitForest H [c]) = true ∧ (splitForest H [c]).length ≤ H.length+1 at second
 by_cases existsFirst : ∃ B, B ∈ F ∧ BinaryExchange.mixed B (leaves X).contains = true
 · obtain ⟨B,hB,hmB⟩ := existsFirst
   have aB := mixedX_contains_nonsingleton_sibling hnS sibling hp embS nonsingle hB hmB
   obtain ⟨⟨x,xB,xX⟩,_⟩ := (BinaryExchange.mixed_iff B _).1 hmB
   have xX' : x ∈ leaves X := List.contains_iff_mem.1 xX
   have aW : a ∉ leaves W := by intro h; rcases (Wlabels a).1 h with h | h; exact xa h; exact hac h
   have atW : BinaryExchange.treeAt T w = some W := by rw [source_treeAt]; exact hw
   have occB := BinaryExchange.crossing_occupies T W w B hnT atW
     (fun z hz => block_labels parts.1 hB hz) ⟨⟨x,xB,(Wlabels x).2 (Or.inl xX')⟩,⟨a,aB,aW⟩⟩
   have noSecond : ∀ C, C ∈ H → BinaryExchange.mixed C [c].contains ≠ true := by
     intro C hC hmC
     obtain ⟨D,hD,hDC⟩ := List.mem_flatMap.1 hC
     have sub := BinaryExchange.split_sub D C (leaves X).contains hDC
     obtain ⟨⟨z,zC,zc⟩,⟨d,dC,dc⟩⟩ := (BinaryExchange.mixed_iff C [c].contains).1 hmC
     have z_eq : z = c := by simpa using zc
     subst z
     have dnc : d ≠ c := by simpa using dc
     have cD := sub c zC
     have dD := sub d dC
     have CnoX : ∀ y, y ∈ C → y ∉ leaves X := by
       rcases BinaryExchange.split_mono D (leaves X).contains C hDC with hy | hn
       · exact False.elim (xc (List.contains_iff_mem.1 (hy c zC)))
       · intro y hy; simpa using hn y hy
     have DnoX : ∀ y, y ∈ D → y ∉ leaves X := by
       intro y yD yX
       have mixedD : BinaryExchange.mixed D (leaves X).contains = true :=
         (BinaryExchange.mixed_iff D _).2 ⟨⟨y,yD,by simpa using yX⟩,⟨c,cD,by simpa using xc⟩⟩
       have aD := mixedX_contains_nonsingleton_sibling hnS sibling hp embS nonsingle hD mixedD
       have atAX : subtree S (v ++ [false]) = some (.node (.leaf a) X) := sibling
       exact original_crossing_clusters_exclude_block hnT hnS hw atAX
         ((Wlabels y).2 (Or.inl yX)) ((Wlabels c).2 (Or.inr rfl)) aW
         (by simp [leaves,yX]) (by simp [leaves,Ne.symm hac,xc]) (by simp [leaves])
         ha hD yD cD aD
     have dW : d ∉ leaves W := by intro h; rcases (Wlabels d).1 h with h | h; exact DnoX d dD h; exact dnc h
     have occD := BinaryExchange.crossing_occupies T W w D hnT atW
       (fun z hz => block_labels parts.1 hD hz) ⟨⟨c,cD,(Wlabels c).2 (Or.inr rfl)⟩,⟨d,dD,dW⟩⟩
     have neBD : B ≠ D := by intro e; exact DnoX x (e ▸ xB) xX'
     have dj := BinaryExchange.pairwise_mem (fun _ _ h => BinaryExchange.disj_symm h) F embT B D hB hD neBD
     exact dj w ⟨(minimalVertices_correct B T w).1 occB,(minimalVertices_correct D T w).1 occD⟩
   have empty : H.filter (fun C => BinaryExchange.mixed C [c].contains) = [] := List.filter_eq_nil_iff.2 noSecond
   have len := BinaryExchange.splitAll_length H [c].contains
   rw [empty] at len
   have endlen : (splitForest H [c]).length ≤ H.length := by simpa [splitForest] using len
   omega
 · have empty : F.filter (fun B => BinaryExchange.mixed B (leaves X).contains) = [] := by
     apply List.filter_eq_nil_iff.2
     exact fun B hB hm => existsFirst ⟨B,hB,hm⟩
   have len := BinaryExchange.splitAll_length F (leaves X).contains
   rw [empty] at len
   have Hlen : H.length ≤ F.length := by simpa [H,splitForest] using len
   omega

theorem actual_case321_exchange {T S X W : Tree} {v w p : RMAF.Vertex}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S v = some (.node (.node (.leaf a) X) (.leaf c)))
 (hw : subtree T w = some W)
 (Wlabels : ∀ x, x ∈ leaves W ↔ x ∈ leaves X ∨ x = c)
 (ch : CherryAt T p a b)
 (hc : cuts S a b = [v ++ [false,true],v ++ [true]])
 (ha : agreement T S F = true) :
 [a] ∈ F ∨ ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧
 VertexGeometry.Refines G (pendantPartition S a b) := by
 by_cases singleA : [a] ∈ F
 · exact Or.inl singleA
 · right
   rcases actual_pendant_safety hnS ha ch with single | single | ref
   · exact False.elim (singleA single)
   · have save : (splitTwo F S (v ++ [false,true]) (v ++ [true])).length ≤ F.length+1 := by
       have hq : subtree S (v ++ [false,true]) = some X := by rw [subtree_append he]; rfl
       have hr : subtree S (v ++ [true]) = some (.leaf c) := by rw [subtree_append he]; rfl
       rw [splitTwo,source_subtree_labels hq,source_subtree_labels hr]
       exact case321_split_saving hnT hnS he hw Wlabels ha singleA
     exact actual_hard2_exchange_from_split_saving_b hnT hnS same ha ch hc single save
   · exact ⟨F,ha,Nat.le_refl _,ref⟩

end Universal233.Rule5Local
