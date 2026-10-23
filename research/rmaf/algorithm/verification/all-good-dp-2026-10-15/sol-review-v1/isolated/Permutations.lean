import BlockColors

namespace Universal233.FinalCutRecovery
open RMAF CoreProgram SourceCoverage VertexGeometry RankDichotomy

/-- The output blocks can be reordered into the original blocks after an
individual permutation of each block's labels. The witnessing map does not
change the executable output or its original cut certificate. -/
def BlockPermutation (P Q : List (List Nat)) : Prop :=
  ∃ f : List Nat → List Nat, (Q.map f).Perm P ∧ ∀ b, b ∈ Q → (f b).Perm b

def blockForKey : List (List Nat) → Nat → List Nat
  | [], _ => []
  | b :: bs, k => if b.headD 0 = k then b else blockForKey bs k

theorem blockForKey_head (P : List (List Nat))
    (hn : (P.map (fun b => b.headD 0)).Nodup) (b : List Nat) (hb : b ∈ P) :
    blockForKey P (b.headD 0) = b := by
  induction P with
  | nil => simp at hb
  | cons a P ih =>
    have hh := List.nodup_cons.1 hn
    rcases List.mem_cons.1 hb with he | hb
    · subst b; simp [blockForKey]
    · have he : a.headD 0 ≠ b.headD 0 := by
        intro he
        exact hh.1 (List.mem_map.2 ⟨b,hb,he.symm⟩)
      change (if a.headD 0 = b.headD 0 then a else blockForKey P (b.headD 0)) = b
      rw [ite_eq_right he]
      exact ih hh.2 hb

theorem representative_colors_perm (S : Tree) (color : Nat → Nat) (P Q : List (List Nat))
    (hp : partitionCheck (leaves S) P = true) (hq : partitionCheck (leaves S) Q = true)
    (hmp : ∀ b, b ∈ P → LabelMonochromatic color b)
    (hmq : ∀ b, b ∈ Q → LabelMonochromatic color b)
    (hlp : P.length = inputRank S color) (hlq : Q.length = inputRank S color) :
    (Q.map (fun b => color (b.headD 0))).Perm (P.map (fun b => color (b.headD 0))) := by
  apply (List.perm_ext_iff_of_nodup (rank_representatives_nodup S color Q hq hmq hlq)
    (rank_representatives_nodup S color P hp hmp hlp)).2
  intro i
  constructor
  · intro hi
    obtain ⟨b,hb,rfl⟩ := List.mem_map.1 hi
    have hx := head_mem b (partitionCheck_nonempty _ Q hq b hb)
    have hxS := partitionCheck_subset _ Q hq (List.mem_flatten.2 ⟨b,hb,hx⟩)
    obtain ⟨c,hc,hxc⟩ := Integration.partitionCheck_covers _ P hp _ hxS
    exact List.mem_map.2 ⟨c,hc,(hmp c hc _ _ hxc (head_mem c (partitionCheck_nonempty _ P hp c hc))).symm⟩
  · intro hi
    obtain ⟨b,hb,rfl⟩ := List.mem_map.1 hi
    have hx := head_mem b (partitionCheck_nonempty _ P hp b hb)
    have hxS := partitionCheck_subset _ P hp (List.mem_flatten.2 ⟨b,hb,hx⟩)
    obtain ⟨c,hc,hxc⟩ := Integration.partitionCheck_covers _ Q hq _ hxS
    exact List.mem_map.2 ⟨c,hc,(hmq c hc _ _ hxc (head_mem c (partitionCheck_nonempty _ Q hq c hc))).symm⟩

theorem block_nodup (P : List (List Nat)) (hn : P.flatten.Nodup)
    (b : List Nat) (hb : b ∈ P) : b.Nodup := by
  induction P with
  | nil => simp at hb
  | cons a P ih =>
    have hh := List.nodup_append.1 (show (a ++ P.flatten).Nodup from hn)
    rcases List.mem_cons.1 hb with he | hb
    · simpa [he] using hh.1
    · exact ih hh.2.1 hb

theorem checked_block_permutation (S : Tree) (P Q : List (List Nat))
    (hp : partitionCheck (leaves S) P = true) (hq : partitionCheck (leaves S) Q = true)
    (hmq : ∀ b, b ∈ Q → LabelMonochromatic (blockColor P) b)
    (hlq : Q.length = P.length) : BlockPermutation P Q := by
  have hnP := checked_flatten_nodup S P hp
  have hnQ := checked_flatten_nodup S Q hq
  have hrep := representative_nodup P hnP (partitionCheck_nonempty _ P hp)
  let f := fun b : List Nat => blockForKey P (blockColor P (b.headD 0))
  have hfP : P.map f = P := by
    calc P.map f = P.map id := by
           apply List.map_congr_left
           intro b hb
           have hh := head_mem b (partitionCheck_nonempty _ P hp b hb)
           dsimp [f]
           rw [color_of_mem P hnP b hb _ hh]
           exact blockForKey_head P hrep b hb
         _ = P := List.map_id P
  have hkeys := representative_colors_perm S (blockColor P) P Q hp hq
    (checked_monochromatic S P hp) hmq (checked_rank S P hp).symm
    (hlq.trans (checked_rank S P hp).symm)
  refine ⟨f,?_,?_⟩
  · have hmap := hkeys.map (blockForKey P)
    simp only [List.map_map,Function.comp_def] at hmap
    change (Q.map f).Perm (P.map f) at hmap
    rw [hfP] at hmap
    exact hmap
  · intro b hb
    have hhb := head_mem b (partitionCheck_nonempty _ Q hq b hb)
    have hy := partitionCheck_subset _ Q hq (List.mem_flatten.2 ⟨b,hb,hhb⟩)
    obtain ⟨c,hc,hyc⟩ := Integration.partitionCheck_covers _ P hp _ hy
    have hhc := head_mem c (partitionCheck_nonempty _ P hp c hc)
    have hcol := color_of_mem P hnP c hc _ hyc
    have hfc : f b = c := by dsimp [f]; rw [hcol]; exact blockForKey_head P hrep c hc
    rw [hfc]
    have hndc : c.Nodup := by
      exact block_nodup P hnP c hc
    have hndb : b.Nodup := by
      exact block_nodup Q hnQ b hb
    apply (List.perm_ext_iff_of_nodup hndc hndb).2
    intro x
    rw [checked_separation S P hp c hc x,
      rank_partition_color_classes S (blockColor P) Q hq hmq
        (hlq.trans (checked_rank S P hp).symm) b hb x]
    rw [color_of_mem P hnP c hc _ hhc,hcol]

theorem all_congr_on {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x, x ∈ xs → f x = g x) : xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.all_cons]; rw [h x (by simp),ih (fun y hy => h y (by simp [hy]))]

theorem selected_contains_perm {b c : List Nat} (h : b.Perm c) (x : Nat) :
    b.contains x = c.contains x := by
  by_cases hx : x ∈ b
  · have hy := h.mem_iff.1 hx; simp [hx,hy]
  · have hy : x ∉ c := fun hy => hx (h.mem_iff.2 hy); simp [hx,hy]

theorem restrict_label_perm (T : Tree) {b c : List Nat} (h : b.Perm c) :
    restrict b T = restrict c T := by
  induction T with
  | leaf x => simp only [restrict,selected_contains_perm h x]
  | node l r ihl ihr => simp only [restrict,ihl,ihr]

theorem span_label_perm (T : Tree) {b c : List Nat} (h : b.Perm c) :
    rootedSpan b T = rootedSpan c T := by
  induction T with
  | leaf x => simp only [rootedSpan,selected_contains_perm h x]
  | node l r ihl ihr => simp only [rootedSpan,ihl,ihr]

theorem minimal_label_perm (T : Tree) {b c : List Nat} (h : b.Perm c) :
    minimalVertices b T = minimalVertices c T := by
  induction T with
  | leaf x => simp only [minimalVertices,selected_contains_perm h x]
  | node l r ihl ihr => simp only [minimalVertices,span_label_perm l h,span_label_perm r h,ihl,ihr]

theorem flatten_map_perm (Q : List (List Nat)) (f : List Nat → List Nat)
    (h : ∀ b, b ∈ Q → (f b).Perm b) : (Q.map f).flatten.Perm Q.flatten := by
  induction Q with
  | nil => exact List.Perm.refl _
  | cons b Q ih =>
      simpa only [List.map_cons,List.flatten_cons] using
        (h b (by simp)).append (ih (fun c hc => h c (by simp [hc])))

theorem partitionCheck_congr (L : List Nat) (P Q : List (List Nat))
    (hflat : P.flatten.Perm Q.flatten)
    (hne : P.all (fun b => !b.isEmpty) = Q.all (fun b => !b.isEmpty)) :
    partitionCheck L P = partitionCheck L Q := by
  have hc : (fun x => P.flatten.count x == 1) = (fun x => Q.flatten.count x == 1) := by
    funext x; rw [hflat.count_eq x]
  simp only [partitionCheck,hne,hc,hflat.all_eq]

theorem partitionCheck_outer_perm (L : List Nat) {P Q : List (List Nat)} (h : P.Perm Q) :
    partitionCheck L P = partitionCheck L Q :=
  partitionCheck_congr L P Q h.flatten h.all_eq

theorem partitionCheck_inner_perm (L : List Nat) (Q : List (List Nat)) (f : List Nat → List Nat)
    (h : ∀ b, b ∈ Q → (f b).Perm b) : partitionCheck L (Q.map f) = partitionCheck L Q := by
  apply partitionCheck_congr L _ _ (flatten_map_perm Q f h)
  simp only [List.all_map]
  apply all_congr_on
  intro b hb
  change Bool.not (f b).isEmpty = Bool.not b.isEmpty
  rw [(h b hb).isEmpty_eq]

theorem disjoint_symm (a b : List RMAF.Vertex) (h : disjointVertices a b = true) :
    disjointVertices b a = true := by
  apply List.all_eq_true.2
  intro v hv
  by_cases ha : v ∈ a
  · have hh := List.all_eq_true.1 h v ha
    simp [hv] at hh
  · simp [ha]

theorem embeddings_pairwise (T : Tree) (P : List (List Nat)) :
    pairwiseEmbeddings T P = true ↔
      P.Pairwise (fun b c => disjointVertices (minimalVertices b T) (minimalVertices c T) = true) := by
  induction P with
  | nil => simp [pairwiseEmbeddings]
  | cons b P ih => simp [pairwiseEmbeddings,List.pairwise_cons,List.all_eq_true,ih]

theorem embeddings_outer_perm (T : Tree) {P Q : List (List Nat)} (h : P.Perm Q) :
    pairwiseEmbeddings T P = pairwiseEmbeddings T Q := by
  apply Bool.eq_iff_iff.2
  rw [embeddings_pairwise,embeddings_pairwise]
  exact h.pairwise_iff (fun hd => disjoint_symm _ _ hd)

theorem embeddings_inner_perm (T : Tree) (Q : List (List Nat)) (f : List Nat → List Nat)
    (h : ∀ b, b ∈ Q → (f b).Perm b) : pairwiseEmbeddings T (Q.map f) = pairwiseEmbeddings T Q := by
  induction Q with
  | nil => rfl
  | cons b Q ih =>
    simp only [List.map_cons,pairwiseEmbeddings,List.all_map]
    rw [ih (fun c hc => h c (by simp [hc]))]
    congr 1
    apply all_congr_on
    intro c hc
    simp only [Function.comp_def]
    rw [minimal_label_perm T (h b (by simp)),minimal_label_perm T (h c (by simp [hc]))]

theorem agreement_outer_perm (T S : Tree) {P Q : List (List Nat)} (h : P.Perm Q) :
    agreement T S P = agreement T S Q := by
  simp only [agreement,partitionCheck_outer_perm _ h,h.all_eq,embeddings_outer_perm _ h]

theorem agreement_inner_perm (T S : Tree) (Q : List (List Nat)) (f : List Nat → List Nat)
    (h : ∀ b, b ∈ Q → (f b).Perm b) : agreement T S (Q.map f) = agreement T S Q := by
  have ha : (Q.map f).all (restrictionAgrees T S) = Q.all (restrictionAgrees T S) := by
    simp only [List.all_map]
    apply all_congr_on
    intro b hb
    simp only [Function.comp_def,restrictionAgrees,restrict_label_perm T (h b hb),restrict_label_perm S (h b hb)]
  simp only [agreement,partitionCheck_inner_perm _ Q f h,ha,embeddings_inner_perm _ Q f h]

/-- Literal ordinary agreement is invariant under the actual block/label
permutations proved for recovery. Original input trees are retained. -/
theorem agreement_block_permutation (T S : Tree) (P Q : List (List Nat))
    (h : BlockPermutation P Q) : agreement T S P = agreement T S Q := by
  obtain ⟨f,hp,hf⟩ := h
  exact (agreement_outer_perm T S hp).symm.trans (agreement_inner_perm T S Q f hf)

end Universal233.FinalCutRecovery
