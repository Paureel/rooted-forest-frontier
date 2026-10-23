import FinalInterface
namespace Universal233.Rule5SourceOrientation
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5FinalClassification

/-- Two literal, successive original-source splits. It is not an edge union
on suppressed displays. The permanent partition stays in original labels. -/
def splitTwo (F : List (List Nat)) (S : Tree) (q r : RMAF.Vertex) :=
 splitForest (splitForest F (subtreeLabels S q)) (subtreeLabels S r)

theorem splitTwo_original {T S : Tree} {F : List (List Nat)}
 {a b : Nat} {q r : RMAF.Vertex} (hn : (leaves S).Nodup)
 (hc : cuts S a b = [q,r] ∨ cuts S a b = [r,q]) (ha : agreement T S F = true) :
 agreement T S (splitTwo F S q r) = true ∧ (splitTwo F S q r).length ≤ F.length+2 := by
 have qm : q ∈ cuts S a b := by rcases hc with h | h <;> simp [h]
 have rm : r ∈ cuts S a b := by rcases hc with h | h <;> simp [h]
 obtain ⟨Q,hQ⟩ := ((cuts_spec S a b q).1 qm).1
 obtain ⟨R,hR⟩ := ((cuts_spec S a b r).1 rm).1
 have h1 := split_original_agreement hn hQ ha
 have h2 := split_original_agreement hn hR h1.1
 rw [←source_subtree_labels hQ] at h1 h2
 rw [←source_subtree_labels hR] at h2
 exact ⟨h2.1,by dsimp [splitTwo]; omega⟩

theorem splitTwo_refines {T S : Tree} {F : List (List Nat)}
 {a b : Nat} {q r : RMAF.Vertex}
 (hc : cuts S a b = [q,r] ∨ cuts S a b = [r,q]) (ha : agreement T S F = true) :
 VertexGeometry.Refines (splitTwo F S q r) (pendantPartition S a b) := by
 intro B hB
 obtain ⟨C,hC,hCB⟩ := List.mem_flatMap.1 hB
 obtain ⟨D,hD,hDC⟩ := List.mem_flatMap.1 hC
 have subBC := BinaryExchange.split_sub C B (subtreeLabels S r).contains hCB
 have subCD := BinaryExchange.split_sub D C (subtreeLabels S q).contains hDC
 rcases BinaryExchange.split_mono C (subtreeLabels S r).contains B hCB with rb | rn
 · refine ⟨subtreeLabels S r,by rcases hc with h | h <;> simp [pendantPartition,h],?_⟩
   exact fun x hx => List.contains_iff_mem.1 (rb x hx)
 · rcases BinaryExchange.split_mono D (subtreeLabels S q).contains C hDC with qb | qn
   · refine ⟨subtreeLabels S q,by rcases hc with h | h <;> simp [pendantPartition,h],?_⟩
     exact fun x hx => List.contains_iff_mem.1 (qb x (subBC x hx))
   · refine ⟨coreLabels S a b,by simp [pendantPartition],?_⟩
     intro x hx
     refine (mem_core S a b x).2 ⟨block_labels (source_agreement_checks ha).1 hD
       (subCD x (subBC x hx)),?_⟩
     intro p hp
     have casesp : p = q ∨ p = r := by rcases hc with h | h <;> simpa [h,or_comm] using hp
     rcases casesp with rfl | rfl
     · have z := qn x (subBC x hx); simpa using z
     · have z := rn x hx; simpa using z

theorem splitTwo_singleton {S : Tree} {F : List (List Nat)} {a b x : Nat}
 {q r : RMAF.Vertex} (hc : cuts S a b = [q,r] ∨ cuts S a b = [r,q])
 (hl : x ∈ leaves S) (hx : x = a ∨ x = b) (hs : [x] ∈ F) :
 [x] ∈ splitTwo F S q r := by
 have qm : q ∈ cuts S a b := by rcases hc with h | h <;> simp [h]
 have rm : r ∈ cuts S a b := by rcases hc with h | h <;> simp [h]
 exact split_endpoint_survives _
   (split_endpoint_survives _ hs (source_label_outside_pendant qm hx hl))
   (source_label_outside_pendant rm hx hl)

/-- Original graph split/coarsen construction with either actual cut order.
The selected consumers derive the split-length saving from their local
geometry. Every returned G is an original agreement forest. -/
theorem actual_hard2_exchange_from_split_saving
 {T S : Tree} {F : List (List Nat)} {p q r : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (ha : agreement T S F = true) (ch : CherryAt T p a b)
 (hc : cuts S a b = [q,r] ∨ cuts S a b = [r,q]) (singleton : [a] ∈ F)
 (saving : (splitTwo F S q r).length ≤ F.length+1) :
 ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧
   VertexGeometry.Refines G (pendantPartition S a b) := by
 have hab := cherry_distinct hnT ch
 have labs := agreement_cherry_source_labels ha ch
 have hspl := splitTwo_original hnS hc ha
 have href := splitTwo_refines hc ha
 have hp := pendant_partition_check hnS labs.1 (b:=b)
 have he := source_embeddings (a:=a) (b:=b) hnS
 have state := OutputState.original_to_state T S (pendantPartition S a b)
   (splitTwo F S q r) hnT hnS same hp hspl.1 href
 obtain ⟨U,hU,chU⟩ := core_has_cherry hnS labs.1 labs.2 hab
 have Uin : U ∈ OutputState.sourceForest S (pendantPartition S a b) :=
   (OutputState.source_component S _ U).2 ⟨coreLabels S a b,by simp [pendantPartition],hU⟩
 have hs := splitTwo_singleton hc labs.1 (Or.inl rfl) singleton
 obtain ⟨G,hG,hlen⟩ := state_save_singleton state (hasCherry_bool (actual_hasCherry ch))
   Uin (hasCherry_bool chU) hs hab
 have out := OutputState.state_to_original T S (pendantPartition S a b) G hnS same hp he hG
 exact ⟨G,out.1,by omega,out.2⟩

theorem actual_hard2_exchange_from_split_saving_b
 {T S : Tree} {F : List (List Nat)} {p q r : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (ha : agreement T S F = true) (ch : CherryAt T p a b)
 (hc : cuts S a b = [q,r] ∨ cuts S a b = [r,q]) (singleton : [b] ∈ F)
 (saving : (splitTwo F S q r).length ≤ F.length+1) :
 ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧
   VertexGeometry.Refines G (pendantPartition S a b) := by
 have hab := cherry_distinct hnT ch
 have labs := agreement_cherry_source_labels ha ch
 have hspl := splitTwo_original hnS hc ha
 have href := splitTwo_refines hc ha
 have hp := pendant_partition_check hnS labs.1 (b:=b)
 have he := source_embeddings (a:=a) (b:=b) hnS
 have state := OutputState.original_to_state T S (pendantPartition S a b)
   (splitTwo F S q r) hnT hnS same hp hspl.1 href
 obtain ⟨U,hU,chU⟩ := core_has_cherry hnS labs.1 labs.2 hab
 have Uin : U ∈ OutputState.sourceForest S (pendantPartition S a b) :=
   (OutputState.source_component S _ U).2 ⟨coreLabels S a b,by simp [pendantPartition],hU⟩
 have hs := splitTwo_singleton hc labs.2 (Or.inr rfl) singleton
 obtain ⟨G,hG,hlen⟩ := state_save_singleton state
   (cherry_bool_swap (hasCherry_bool (actual_hasCherry ch)))
   Uin (cherry_bool_swap (hasCherry_bool chU)) hs (Ne.symm hab)
 have out := OutputState.state_to_original T S (pendantPartition S a b) G hnS same hp he hG
 exact ⟨G,out.1,by omega,out.2⟩

end Universal233.Rule5SourceOrientation
