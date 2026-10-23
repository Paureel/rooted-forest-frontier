import Rule4Graft

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

theorem shared_label_block_equal {T : Tree} {F : List (List Nat)}
    (hp : partitionCheck (leaves T) F = true) (he : pairwiseEmbeddings T F = true)
    {B H : List Nat} (hB : B ∈ F) (hH : H ∈ F) {x : Nat} (hxB : x ∈ B) (hxH : x ∈ H) : B = H := by
  obtain ⟨v,hv⟩ := leaf_exists (block_labels hp hB hxB)
  exact checked_support_unique T F he B H hB hH v
    ((minimalVertices_terminal B T v x hv).2 hxB)
    ((minimalVertices_terminal H T v x hv).2 hxH)

theorem checked_blocks_clear {T : Tree} {F : List (List Nat)}
    (he : pairwiseEmbeddings T F = true)
    {B H : List Nat} (hB : B ∈ F) (hH : H ∈ F) (hne : B ≠ H) :
    Disj T B H := by
  intro v hv
  exact hne (checked_support_unique T F he B H hB hH v
    ((minimalVertices_correct B T v).2 hv.1)
    ((minimalVertices_correct H T v).2 hv.2))

theorem singleton_clear {S : Tree} (hn : (leaves S).Nodup)
    {c : Nat} (hc : c ∈ leaves S) (E : List Nat) (hce : c ∉ E) :
    Disj S [c] E := by
  obtain ⟨w,hw⟩ := leaf_exists hc
  intro v hv
  obtain ⟨u,z,hu,hz,hp⟩ := hv.1
  have one : ∀ q, selectedLeaves [c] S q → q = w := by
    intro q hq
    exact leaf_unique hn ((leafAt_selected S q c).2 hq) hw
  have hu' := one u hu
  have hz' := one z hz
  subst u; subst z
  have hvw := path_identical v w hp
  subst v
  exact hce ((minimalVertices_terminal E S w c hw).1 ((minimalVertices_correct E S w).2 hv.2))

theorem treeAt_eq_subtree (S : Tree) (q : RMAF.Vertex) : treeAt S q = subtree S q := by
  induction q generalizing S with
  | nil => cases S <;> rfl
  | cons s q ih =>
    cases S with
    | leaf x => rfl
    | node l r => cases s <;> exact ih _

theorem subtreeLabels_eq_leaves {S U : Tree} {q : RMAF.Vertex}
    (h : subtree S q = some U) : subtreeLabels S q = leaves U := by
  induction q generalizing S with
  | nil =>
    have he : S = U := Option.some.inj h
    subst U
    rfl
  | cons s q ih =>
    cases S with
    | leaf x => simp [subtree] at h
    | node l r => cases s <;> exact ih h

/-- Any two original label subsets on opposite sides of an original descendant
edge have disjoint ORIGINAL minimal embeddings. No branch-safety premise. -/
theorem original_clade_clear {S U : Tree} (hn : (leaves S).Nodup)
    {q : RMAF.Vertex} (hq : treeAt S q = some U) (H E : List Nat)
    (hHl : H ⊆ leaves S) (hEl : E ⊆ leaves S)
    (hHi : H ⊆ leaves U) (hEo : ∀ x, x ∈ E → x ∉ leaves U) : Disj S H E := by
  have cluster := subtree_cluster S U q hn hq
  have hdis := cluster_disjoint (leaves S) ((leaves U).contains ·) S
    (cluster_weaken cluster (by intro x hx; trivial))
  have hh := (executable_disjointVertices S _ _).1 hdis
  exact disj_mono hh
    (by intro x hx; exact List.mem_filter.2 ⟨hHl hx,by simpa using hHi hx⟩)
    (by intro x hx; exact List.mem_filter.2 ⟨hEl hx,by simpa using hEo x hx⟩)

/-- The disputed case's new E is clear of EVERY untouched source block,
including blocks in X2 and blocks outside the a--b LCA clade. Retained-source
cherry and original source path guards are consumed, not desired clearance. -/
theorem source_extension_all_clear {T S : Tree} {F : List (List Nat)}
    (hn : (leaves S).Nodup) (hF : agreement T S F = true)
    {a b c : Nat} (hab : a ≠ b)
    {q r : RMAF.Vertex} (hcuts : (pendantOriginal S a b).Perm [q,r])
    (hql : subtreeLabels S q = [c])
    {B : List Nat} (hB : B ∈ F) (ha : a ∈ B) (hcB : c ∉ B)
    (hb : [b] ∈ F) (hc : [c] ∈ F)
    (hd : ∃ d, d ∈ B ∧ d ∈ subtreeLabels S r) :
    let K := no B ((subtreeLabels S r).contains ·)
    ∀ H, H ∈ F → H ≠ B → H ≠ [b] → Disj S H (b :: K) := by
  let K := no B ((subtreeLabels S r).contains ·)
  let C := (leaves S).filter (fun x => !(subtreeLabels S q).contains x && !(subtreeLabels S r).contains x)
  change ∀ H, H ∈ F → H ≠ B → H ≠ [b] → Disj S H (b :: K)
  have checks := source_agreement_checks hF
  have hq : q ∈ pendantOriginal S a b := two_cut_mem_left hcuts
  have hr : r ∈ pendantOriginal S a b := two_cut_mem_right hcuts
  have hrv := (pendantOriginal_spec S a b r).1 hr
  have hal : a ∈ leaves S := block_labels checks.1 hB ha
  have hbl : b ∈ leaves S := block_labels checks.1 hb (by simp)
  have hend := hard2_endpoints_in_root hq hr hal hbl
  have haR : a ∉ subtreeLabels S r := source_label_outside_pendant hr (Or.inl rfl) hal
  have hbR : b ∉ subtreeLabels S r := source_label_outside_pendant hr (Or.inr rfl) hbl
  have haK : a ∈ K := by simp [K,no,ha,haR]
  have hKC : K ⊆ C := by
    intro x hx
    have hh := List.mem_filter.1 hx
    have hxB : x ∈ B := hh.1
    have hxc : x ≠ c := fun he => hcB (he ▸ hxB)
    simp only [C,List.mem_filter,List.contains_iff_mem,Bool.and_eq_true,Bool.not_eq_true']
    exact ⟨block_labels checks.1 hB hxB,by simpa [hql] using hxc,by simpa using hh.2⟩
  have hbC : b ∈ C := hend.2
  have hEl : (b :: K) ⊆ leaves S := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hbl
    · exact block_labels checks.1 hB (List.mem_filter.1 hx).1
  have hEo : ∀ x, x ∈ b :: K → x ∉ subtreeLabels S r := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hbR
    · exact by simpa using (List.mem_filter.1 hx).2
  obtain ⟨U,hU,hch⟩ := literal_root_cherry hn hal hbl hab hcuts
  obtain ⟨d,hdB,hdR⟩ := hd
  have hparent := crossing_boundary_parent hrv.2.1 B ha hdB hal hdR haR
  intro H hH hHB hHb
  have haH : a ∉ H := by
    intro hh
    exact hHB (shared_label_block_equal checks.1 checks.2 hH hB hh ha)
  have hbH : b ∉ H := by
    intro hh
    exact hHb (shared_label_block_equal checks.1 checks.2 hH hb hh (by simp))
  have hHl : H ⊆ leaves S := by intro x hx; exact block_labels checks.1 hH hx
  have hHK : Disj S H K := disj_mono
    (checked_blocks_clear checks.2 hH hB hHB) (fun _ hx => hx)
    (by intro x hx; exact (List.mem_filter.1 hx).1)
  by_cases hcH : c ∈ H
  · have hHeq : H = [c] := shared_label_block_equal checks.1 checks.2 hH hc hcH (by simp)
    subst H
    have hce : c ∉ b :: K := by
      have hcb : c ≠ b := by
        intro he
        have hh := source_label_outside_pendant hq (Or.inr rfl) hbl
        simp [hql,he] at hh
      simp [K,no,hcb,hcB]
    exact singleton_clear hn (block_labels checks.1 hc (by simp)) _ hce
  · by_cases hmeet : ∃ x, x ∈ H ∧ x ∈ subtreeLabels S r
    · obtain ⟨x,hx,hxr⟩ := hmeet
      have hmono := source_boundary_mono hn hF hB hH hHB hrv.2.1 hparent
      have hHi : H ⊆ subtreeLabels S r := by intro y hy; exact (hmono x y hx hy).1 hxr
      obtain ⟨V,hV⟩ := hrv.1
      have hlabels := subtreeLabels_eq_leaves hV
      have ht : treeAt S r = some V := by rw [treeAt_eq_subtree]; exact hV
      exact original_clade_clear hn ht H (b :: K) hHl hEl
        (by simpa only [hlabels] using hHi)
        (by simpa only [hlabels] using hEo)
    · have hHC : H ⊆ C := by
        intro x hx
        have hxR : x ∉ subtreeLabels S r := fun hh => hmeet ⟨x,hx,hh⟩
        have hxc : x ≠ c := fun he => hcH (he ▸ hx)
        simp [C,hHl hx,hql,hxc,hxR]
      exact (executable_disjointVertices S H (b :: K)).1
        (retained_source_extension_clear hn C hU hch H K hHC hKC hbC haK haH hbH
          ((executable_disjointVertices S H K).2 hHK))
end Universal233.Rule4
