import T1Split
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

theorem hasCherry_bool {T : Tree} {a b : Nat} (hc : HasCherry a b T) :
 ForestState.cherry a b T = true := by
 induction hc with
 | here => simp [ForestState.cherry]
 | swap => simp [ForestState.cherry]
 | left hc ih => simp [ForestState.cherry,ih]
 | right hc ih => simp [ForestState.cherry,ih]

theorem cherry_bool_swap {T : Tree} {a b : Nat} (hc : ForestState.cherry a b T = true) :
 ForestState.cherry b a T = true := by
 obtain ⟨p,hp⟩ := ForestState.cherry_at_exists T a b hc
 exact hp.symm.to_cherry

theorem cherry_distinct {T : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hn : (leaves T).Nodup) (hc : CoreGraph.CherryAt T p a b) : a ≠ b := by
 have nod := (subtreeLabels_sublist T p).nodup hn
 rw [source_subtree_labels hc] at nod
 simpa [leaves] using nod

/-- Actual common-cherry coarsening saves exactly one block when the chosen
original endpoint is a singleton. No merely no-larger bound is substituted. -/
theorem state_save_singleton {T U : Tree} {ss : List Tree} {H : List (List Nat)}
 {a b : Nat} (hag : ForestState.agrees (some T) ss H = true)
 (cht : ForestState.cherry a b T = true) (hu : U ∈ ss)
 (chu : ForestState.cherry a b U = true) (hs : [a] ∈ H) (hab : a ≠ b) :
 ∃ G, ForestState.agrees (some T) ss G = true ∧ G.length+1 = H.length := by
 have hp := (ForestState.agrees_parts _ _ _ hag).2.1
 obtain ⟨p,hpT⟩ := ForestState.cherry_at_exists T a b cht
 obtain ⟨B,hB,hbB⟩ := partitionCheck_covers (leaves T) H hp b hpT.labels.2
 have haB : a ∉ B := by
   intro hm
   have e := ForestState.checked_unique_block (leaves T) H hp B [a] hB hs a hm (by simp)
   have eb : b = a := by simpa [e] using hbB
   exact hab eb.symm
 let G := ForestState.reassignedForest H B a
 have hagG := ForestState.reassignment_preserves_agreement T ss H b a B hag
   (cherry_bool_swap cht) U hu (cherry_bool_swap chu) hB hs hbB haB
 have hlen := ForestState.reassignment_length (leaves T) H B a hp hB hs haB
 exact ⟨G,hagG,hlen⟩

/-- The original t1 exchange, proved by one literal source-edge split followed
by a common-cherry coarsening. The input is the ORIGINAL ordinary agreement. -/
theorem actual_t1_pendant_exchange {T S : Tree} {F : List (List Nat)}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (ha : agreement T S F = true)
 {p : RMAF.Vertex} {a b : Nat} (hc : CoreGraph.CherryAt T p a b)
 (one : (cuts S a b).length = 1) :
 ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧ Refines G (pendantPartition S a b) := by
 have hab := cherry_distinct hnT hc
 have labs := agreement_cherry_source_labels ha hc
 obtain ⟨q,hq⟩ := List.length_eq_one_iff.1 one
 have qmem : q ∈ cuts S a b := by simp [hq]
 have qvalid := ((cuts_spec S a b q).1 qmem).1
 obtain ⟨Uq,hUq⟩ := qvalid
 have Xeq : subtreeLabels S q = leaves Uq := source_subtree_labels hUq
 let H := splitForest F (subtreeLabels S q)
 have hsplit : agreement T S H = true ∧ H.length ≤ F.length+1 := by
   simpa only [H,Xeq] using split_original_agreement hnS hUq ha
 have href : Refines H (pendantPartition S a b) := split_refines_one ha hq
 have hp : partitionCheck (leaves S) (pendantPartition S a b) = true := pendant_partition_check hnS labs.1
 have he := source_embeddings (a:=a) (b:=b) hnS
 have state := OutputState.original_to_state T S (pendantPartition S a b) H hnT hnS same hp hsplit.1 href
 obtain ⟨U,hU,chU⟩ := core_has_cherry hnS labs.1 labs.2 hab
 have Uin : U ∈ OutputState.sourceForest S (pendantPartition S a b) :=
   (OutputState.source_component S _ U).2 ⟨coreLabels S a b,by simp [pendantPartition],hU⟩
 have cht := hasCherry_bool (actual_hasCherry hc)
 have chu := hasCherry_bool chU
 have finish : ∀ G, ForestState.agrees (some T) (OutputState.sourceForest S (pendantPartition S a b)) G = true →
     G.length+1 = H.length →
     agreement T S G = true ∧ G.length ≤ F.length ∧ Refines G (pendantPartition S a b) := by
   intro G hG hlen
   have hh := OutputState.state_to_original T S (pendantPartition S a b) G hnS same hp he hG
   exact ⟨hh.1,by omega,hh.2⟩
 rcases actual_pendant_safety hnS ha hc with hs | hs | hFref
 · have haX := source_label_outside_pendant qmem (Or.inl rfl) labs.1
   have hsH : [a] ∈ H := split_endpoint_survives _ hs haX
   obtain ⟨G,hG,hlen⟩ := state_save_singleton state cht Uin chu hsH hab
   exact ⟨G,finish G hG hlen⟩
 · have hbX := source_label_outside_pendant qmem (Or.inr rfl) labs.2
   have hsH : [b] ∈ H := split_endpoint_survives _ hs hbX
   obtain ⟨G,hG,hlen⟩ := state_save_singleton state (cherry_bool_swap cht) Uin (cherry_bool_swap chu) hsH (Ne.symm hab)
   exact ⟨G,finish G hG hlen⟩
 · exact ⟨F,ha,Nat.le_refl _,hFref⟩
end Universal233.CherryBranching
