import Rule5Case321
namespace Universal233.Rule5Case322
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local
set_option maxRecDepth 10000

/-- In the actual displayed source bottom, a block with X,c and an outside
label must be the block containing b whenever b is nonsingleton. This follows
from occupancy of the original parent of b; no saving premise is supplied. -/
theorem source_three_part_contains_b {T S X : Tree} {w : RMAF.Vertex}
 {F : List (List Nat)} {D : List Nat} {a b c x d : Nat}
 (hnS : (leaves S).Nodup)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (ha : agreement T S F = true) (hD : D ∈ F)
 (xD : x ∈ D) (cD : c ∈ D) (dD : d ∈ D)
 (xX : x ∈ leaves X)
 (dV : d ∉ leaves (.node (.node (.leaf a) X) (.leaf c)))
 (nonsingle : [b] ∉ F) : b ∈ D := by
 apply Classical.byContradiction
 intro noB
 have parts := BinaryExchange.agreement_parts T S F ha
 have hp := parts.2.1
 have emb := parts.2.2.2.2
 have hb : LeafAt S (w ++ [true]) b := by rw [LeafAt,subtree_append he]; rfl
 obtain ⟨B,hB,bB⟩ := partitionCheck_covers (leaves S) F hp b (leafAt_label S _ b hb)
 have occB := nonsingleton_block_parent hb hp hB bB nonsingle
 have dnb : d ≠ b := by intro e; subst d; exact noB dD
 have dW : d ∉ leaves (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)) := by
   intro h
   rcases List.mem_append.1 h with h | h
   · exact dV h
   · exact dnb (by simpa [leaves] using h)
 have xW : x ∈ leaves (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)) := by simp [leaves,xX]
 have atW : BinaryExchange.treeAt S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)) := by
   rw [source_treeAt]; exact he
 have occD := BinaryExchange.crossing_occupies S _ w D hnS atW
   (fun z hz => block_labels hp hD hz) ⟨⟨x,xD,xW⟩,⟨d,dD,dW⟩⟩
 have ne : D ≠ B := by intro e; exact noB (e ▸ bB)
 have dj := BinaryExchange.pairwise_mem (fun _ _ h => BinaryExchange.disj_symm h) F emb D B hD hB ne
 exact dj w ⟨(minimalVertices_correct D S w).1 occD,(minimalVertices_correct B S w).1 occB⟩

/-- Source-only split saving in the ordinary Case322 easy alternative.
The guard refers to b's actual original AF block. It is not a saving field. -/
theorem split_saving_without_bcx {T S X : Tree} {w : RMAF.Vertex}
 {F : List (List Nat)} {a b c : Nat}
 (hnS : (leaves S).Nodup)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (ha : agreement T S F = true) (single : [a] ∈ F) (nonsingle : [b] ∉ F)
 (noBCX : ∀ D, D ∈ F → b ∈ D → c ∈ D → ∀ x, x ∈ D → x ∈ leaves X → False) :
 (splitForest (splitForest F (leaves X)) [c]).length ≤ F.length+1 := by
 have base : subtree S (w ++ [false]) = some (.node (.node (.leaf a) X) (.leaf c)) := by
   rw [subtree_append he]; rfl
 obtain ⟨xa,xc,hac⟩ := source_base_proper hnS base
 have parts := BinaryExchange.agreement_parts T S F ha
 have hp := parts.2.1
 have emb := parts.2.2.2.2
 have hq : subtree S (w ++ [false,false,true]) = some X := by rw [subtree_append he]; rfl
 have hr : subtree S (w ++ [false,true]) = some (.leaf c) := by rw [subtree_append he]; rfl
 have first := split_original_agreement hnS hq ha
 let H := splitForest F (leaves X)
 change (splitForest H [c]).length ≤ F.length+1
 change agreement T S H = true ∧ H.length ≤ F.length+1 at first
 have second := split_original_agreement hnS hr first.1
 change agreement T S (splitForest H [c]) = true ∧ (splitForest H [c]).length ≤ H.length+1 at second
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
     have dV : d ∉ leaves (.node (.node (.leaf a) X) (.leaf c)) := by simp [leaves,dna,CnoX d dC,dnc]
     have bD := source_three_part_contains_b hnS he ha hD yD cD dD yX dV nonsingle
     exact noBCX D hD bD cD y yD yX
   have occD := source_cmixed_noX_occupies hnS base hac hp single hD cD DnoX ⟨d,dD,dnc⟩
   have noFirst : ∀ B, B ∈ F → BinaryExchange.mixed B (leaves X).contains ≠ true := by
     intro B hB mixedB
     have occB := source_mixedX_occupies hnS base xa xc hp single hB mixedB
     have neBD : B ≠ D := by
       intro e
       obtain ⟨⟨y,yB,yX⟩,_⟩ := (BinaryExchange.mixed_iff B (leaves X).contains).1 mixedB
       exact DnoX y (e ▸ yB) (List.contains_iff_mem.1 yX)
     have dj := BinaryExchange.pairwise_mem (fun _ _ h => BinaryExchange.disj_symm h) F emb B D hB hD neBD
     exact dj (w ++ [false]) ⟨(minimalVertices_correct B S _).1 occB,(minimalVertices_correct D S _).1 occD⟩
   have empty : F.filter (fun B => BinaryExchange.mixed B (leaves X).contains) = [] := List.filter_eq_nil_iff.2 noFirst
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

/-- Ordinary original-AF no-larger hard2 exchange for the easy Case322
alternative. This returns an original AF refining the original hard2 partition. -/
theorem actual_easy_exchange {T S X : Tree} {w p : RMAF.Vertex}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (ch : CherryAt T p a b)
 (hc : cuts S a b = [w ++ [false,false,true],w ++ [false,true]])
 (ha : agreement T S F = true) (single : [a] ∈ F) (nonsingle : [b] ∉ F)
 (noBCX : ∀ D, D ∈ F → b ∈ D → c ∈ D → ∀ x, x ∈ D → x ∈ leaves X → False) :
 ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧
 VertexGeometry.Refines G (pendantPartition S a b) := by
 apply actual_hard2_exchange_from_split_saving hnT hnS same ha ch hc single
 have hq : subtree S (w ++ [false,false,true]) = some X := by rw [subtree_append he]; rfl
 have hr : subtree S (w ++ [false,true]) = some (.leaf c) := by rw [subtree_append he]; rfl
 rw [splitTwo,source_subtree_labels hq,source_subtree_labels hr]
 exact split_saving_without_bcx hnS he ha single nonsingle noBCX

/-- Both original sibling orientations of the target cherry are admitted. -/
theorem actual_unordered_pendant_safety {T S : Tree} {F : List (List Nat)} {a b : Nat}
 (hnS : (leaves S).Nodup) (ha : agreement T S F = true) (ch : ActualCherry T a b) :
 [a] ∈ F ∨ [b] ∈ F ∨ Refines F (pendantPartition S a b) := by
 obtain ⟨p,ch | ch⟩ := ch
 · exact actual_pendant_safety hnS ha ch
 · rcases actual_pendant_safety hnS ha ch with sb | sa | ref
   · exact Or.inr (Or.inl sb)
   · exact Or.inl sa
   · exact Or.inr (Or.inr (by rw [pendantPartition_swap S a b]; exact ref))

theorem unordered_cherry_distinct {T : Tree} {a b : Nat}
 (hnT : (leaves T).Nodup) (ch : ActualCherry T a b) : a ≠ b := by
 obtain ⟨p,ch | ch⟩ := ch
 · exact cherry_distinct hnT ch
 · exact Ne.symm (cherry_distinct hnT ch)

/-- The easy exchange includes both actual target cherry orientations. -/
theorem actual_easy_exchange_unordered {T S X : Tree} {w : RMAF.Vertex}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (ch : ActualCherry T a b)
 (hc : cuts S a b = [w ++ [false,false,true],w ++ [false,true]])
 (ha : agreement T S F = true) (single : [a] ∈ F) (nonsingle : [b] ∉ F)
 (noBCX : ∀ D, D ∈ F → b ∈ D → c ∈ D → ∀ x, x ∈ D → x ∈ leaves X → False) :
 ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧ Refines G (pendantPartition S a b) := by
 obtain ⟨p,ch | ch⟩ := ch
 · exact actual_easy_exchange hnT hnS same he ch hc ha single nonsingle noBCX
 · have hc' : cuts S b a = [w ++ [false,false,true],w ++ [false,true]] := by rw [←cuts_swap S a b]; exact hc
   have saving : (splitTwo F S (w ++ [false,false,true]) (w ++ [false,true])).length ≤ F.length+1 := by
     have hq : subtree S (w ++ [false,false,true]) = some X := by rw [subtree_append he]; rfl
     have hr : subtree S (w ++ [false,true]) = some (.leaf c) := by rw [subtree_append he]; rfl
     rw [splitTwo,source_subtree_labels hq,source_subtree_labels hr]
     exact split_saving_without_bcx hnS he ha single nonsingle noBCX
   obtain ⟨G,hG,len,ref⟩ := actual_hard2_exchange_from_split_saving_b hnT hnS same ha ch hc' single saving
   exact ⟨G,hG,len,by rw [pendantPartition_swap S a b]; exact ref⟩
end Universal233.Rule5Case322
