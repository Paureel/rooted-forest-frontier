import OrientedSaving
namespace Universal233.Case322Extraction
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322
set_option maxRecDepth 15000

theorem split_two_refines_any_order {T S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {a b c : Nat}
 (hn : (leaves S).Nodup) (he : subtree S w = some (bottom sa sc sb a b c X))
 (two : (cuts S a b).length = 2) (ha : agreement T S F = true) :
 Refines (splitForest (splitForest F (leaves X)) [c]) (pendantPartition S a b) := by
 obtain ⟨qx,qc⟩ := bottom_actual_pendants hn he
 have xlab := source_subtree_labels (bottom_x_lookup he)
 have clab := source_subtree_labels (bottom_c_lookup he)
 have orders := bottom_two_cut_orders hn he two
 have cutCases : ∀ q, q ∈ cuts S a b → q = xArc w sa sc sb ∨ q = cArc w sc sb := by
   intro q hq
   rcases orders with ord | ord
   · simpa [ord] using hq
   · have hh : q = cArc w sc sb ∨ q = xArc w sa sc sb := by simpa [ord] using hq
     exact hh.symm
 intro B hB
 obtain ⟨C,hC,hCB⟩ := List.mem_flatMap.1 hB
 obtain ⟨D,hD,hDC⟩ := List.mem_flatMap.1 hC
 have subBC := BinaryExchange.split_sub C B [c].contains hCB
 have subCD := BinaryExchange.split_sub D C (leaves X).contains hDC
 rcases BinaryExchange.split_mono C [c].contains B hCB with cb | cn
 · refine ⟨subtreeLabels S (cArc w sc sb),by simp only [pendantPartition,List.mem_append,List.mem_map,List.mem_singleton]; exact Or.inl ⟨cArc w sc sb,qc,rfl⟩,?_⟩
   intro x hx
   rw [clab]
   exact List.contains_iff_mem.1 (cb x hx)
 · rcases BinaryExchange.split_mono D (leaves X).contains C hDC with xb | xn
   · refine ⟨subtreeLabels S (xArc w sa sc sb),by simp only [pendantPartition,List.mem_append,List.mem_map,List.mem_singleton]; exact Or.inl ⟨xArc w sa sc sb,qx,rfl⟩,?_⟩
     intro x hx
     rw [xlab]
     exact List.contains_iff_mem.1 (xb x (subBC x hx))
   · refine ⟨coreLabels S a b,by simp [pendantPartition],?_⟩
     intro x hx
     refine (mem_core S a b x).2 ⟨block_labels (source_agreement_checks ha).1 hD (subCD x (subBC x hx)),?_⟩
     intro q hq
     rcases cutCases q hq with rfl | rfl
     · rw [xlab]; have hh := xn x (subBC x hx); simpa using hh
     · rw [clab]; have hh := cn x hx; simpa [leaves] using hh

/-- Arbitrary source and target sibling orders, with original hard2
refinement and derived occupancy saving. Original cuts retain their actual
order; the split construction is allowed a different internal split order. -/
theorem oriented_easy_exchange {T S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (bottom sa sc sb a b c X))
 (ch : ActualCherry T a b) (two : (cuts S a b).length = 2)
 (ha : agreement T S F = true) (single : [a] ∈ F) (nonsingle : [b] ∉ F)
 (noBCX : ∀ D, D ∈ F → b ∈ D → c ∈ D → ∀ x, x ∈ D → x ∈ leaves X → False) :
 OriginalCover T S F (pendantPartition S a b) := by
 let H := splitForest (splitForest F (leaves X)) [c]
 have hx := bottom_x_lookup he
 have hc := bottom_c_lookup he
 have hs1 := split_original_agreement hnS hx ha
 have hs2 := split_original_agreement hnS hc hs1.1
 have hH : agreement T S H = true := hs2.1
 have save : H.length ≤ F.length+1 := oriented_split_saving hnS he ha single nonsingle noBCX
 have href : Refines H (pendantPartition S a b) := split_two_refines_any_order hnS he two ha
 have la := bottom_a_lookup he
 have lb := bottom_b_lookup he
 have al := leafAt_label S _ a la
 have bl := leafAt_label S _ b lb
 have hab := unordered_cherry_distinct hnT ch
 have hp := pendant_partition_check hnS al (b:=b)
 have embeddings := source_embeddings (a:=a) (b:=b) hnS
 have state := OutputState.original_to_state T S (pendantPartition S a b) H hnT hnS same hp hH href
 obtain ⟨U,hU,chU⟩ := core_has_cherry hnS al bl hab
 have Uin : U ∈ OutputState.sourceForest S (pendantPartition S a b) :=
   (OutputState.source_component S _ U).2 ⟨coreLabels S a b,by simp [pendantPartition],hU⟩
 have proper := bottom_proper hnS he
 have hsX := split_endpoint_survives (leaves X) single proper.1
 have hsC := split_endpoint_survives [c] hsX (by simpa using proper.2.2.1)
 have cherryT : ForestState.cherry a b T = true := by
   obtain ⟨p,ch | ch⟩ := ch
   · exact hasCherry_bool (actual_hasCherry ch)
   · exact cherry_bool_swap (hasCherry_bool (actual_hasCherry ch))
 obtain ⟨G,hG,hlen⟩ := state_save_singleton state cherryT Uin (hasCherry_bool chU) hsC hab
 have out := OutputState.state_to_original T S (pendantPartition S a b) G hnS same hp embeddings hG
 exact ⟨G,out.1,by omega,out.2⟩

theorem oriented_hard2_or_b_or_bcx {T S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (bottom sa sc sb a b c X))
 (ch : ActualCherry T a b) (two : (cuts S a b).length = 2)
 (ha : agreement T S F = true) :
 OriginalCover T S F (pendantPartition S a b) ∨ [b] ∈ F ∨
 ([a] ∈ F ∧ ∃ B, B ∈ F ∧ b ∈ B ∧ c ∈ B ∧ ∃ x, x ∈ B ∧ x ∈ leaves X) := by
 rcases actual_unordered_pendant_safety hnS ha ch with singleA | singleB | ref
 · by_cases singleB : [b] ∈ F
   · exact Or.inr (Or.inl singleB)
   · by_cases noBCX : ∀ D, D ∈ F → b ∈ D → c ∈ D → ∀ x, x ∈ D → x ∈ leaves X → False
     · exact Or.inl (oriented_easy_exchange hnT hnS same he ch two ha singleA singleB noBCX)
     · right; right
       refine ⟨singleA,?_⟩
       apply Classical.byContradiction
       intro no
       apply noBCX
       intro D hD bD cD x xD xX
       exact no ⟨D,hD,bD,cD,x,xD,xX⟩
 · exact Or.inr (Or.inl singleB)
 · exact Or.inl ⟨F,ha,Nat.le_refl _,ref⟩
end Universal233.Case322Extraction
