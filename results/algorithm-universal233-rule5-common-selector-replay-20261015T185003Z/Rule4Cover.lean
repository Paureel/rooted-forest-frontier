import Rule4LcaCoverage

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

def pendantPartition (S : Tree) (a b : Nat) : List (List Nat) :=
  let cuts := pendantOriginal S a b
  cuts.map (subtreeLabels S) ++
    [(leaves S).filter (fun x => cuts.all (fun q => !(subtreeLabels S q).contains x))]

def isolatePartition (S : Tree) (a : Nat) : List (List Nat) :=
  [[a],(leaves S).filter (fun x => x != a)]

theorem restrictionAgrees_reverse {T S : Tree} {B : List Nat}
    (h : restrictionAgrees T S B = true) : restrictionAgrees S T B = true := by
  unfold restrictionAgrees at h ⊢
  cases ht : restrict B T <;> cases hs : restrict B S <;> simp only [ht,hs] at h ⊢
  all_goals try contradiction
  exact (sameShape_correct _ _).2 (iso_symm ((sameShape_correct _ _).1 h))

theorem agreement_reverse {T S : Tree} {F : List (List Nat)}
    (h : agreement T S F = true) : agreement S T F = true := by
  obtain ⟨hpT,hpS,hshape,hdT,hdS⟩ := agreement_parts T S F h
  unfold agreement
  simp only [Bool.and_eq_true,List.all_eq_true,executable_pairwiseEmbeddings]
  exact ⟨⟨⟨⟨hpS,hpT⟩,by intro B hB; exact restrictionAgrees_reverse (hshape B hB)⟩,hdS⟩,hdT⟩

theorem common_pair_respects {T S : Tree} {F : List (List Nat)}
    (hn : (leaves S).Nodup) (hF : agreement T S F = true)
    {a b : Nat} (hc : HasCherry a b T) {B : List Nat} (hB : B ∈ F)
    (ha : a ∈ B) (hb : b ∈ B) {q : RMAF.Vertex} (hq : q ∈ pendantOriginal S a b) :
    ∀ C, C ∈ F → ∀ x y, x ∈ C → y ∈ C →
      (x ∈ subtreeLabels S q ↔ y ∈ subtreeLabels S q) := by
  obtain ⟨p,hp | hp⟩ := hasCherry_address hc
  · have h := (pendantOriginal_spec S a b q).1 hq
    exact agreement_respects_pendant hn hF hp hB ha hb h.2.1 h.2.2.1 h.2.2.2
  · have hq' : q ∈ pendantOriginal S b a := by rw [←pendantOriginal_swap S a b]; exact hq
    have h := (pendantOriginal_spec S b a q).1 hq'
    exact agreement_respects_pendant hn hF hp hB hb ha h.2.1 h.2.2.1 h.2.2.2

/-- Every original agreement block respects the literal partition cutting ALL
outgoing original arcs on the path, for arbitrary pendant count. -/
theorem common_pair_all_pendants {T S : Tree} {F : List (List Nat)}
    (hn : (leaves S).Nodup) (hF : agreement T S F = true)
    {a b : Nat} (hc : HasCherry a b T) {B : List Nat} (hB : B ∈ F)
    (ha : a ∈ B) (hb : b ∈ B) :
    VertexGeometry.Refines F (pendantPartition S a b) := by
  have checks := source_agreement_checks hF
  intro C hC
  have hne := (agreement_graph_factors T S F hF).2.2 C hC
  cases C with
  | nil => contradiction
  | cons x xs =>
    by_cases hex : ∃ q, q ∈ pendantOriginal S a b ∧ x ∈ subtreeLabels S q
    · obtain ⟨q,hq,hx⟩ := hex
      refine ⟨subtreeLabels S q,?_,?_⟩
      · apply List.mem_append_left
        exact List.mem_map.2 ⟨q,hq,rfl⟩
      · intro y hy
        exact (common_pair_respects hn hF hc hB ha hb hq _ hC x y (by simp) hy).1 hx
    · refine ⟨(leaves S).filter (fun y => (pendantOriginal S a b).all (fun q => !(subtreeLabels S q).contains y)),?_,?_⟩
      · apply List.mem_append_right; simp
      · intro y hy
        apply List.mem_filter.2
        refine ⟨block_labels checks.1 hC hy,List.all_eq_true.2 ?_⟩
        intro q hq
        have hout : y ∉ subtreeLabels S q := by
          intro hyq
          have hxq := (common_pair_respects hn hF hc hB ha hb hq _ hC x y (by simp) hy).2 hyq
          exact hex ⟨q,hq,hxq⟩
        simpa using hout

theorem singleton_refines_isolate {T S : Tree} {F : List (List Nat)}
    (hF : agreement T S F = true) {a : Nat} (ha : [a] ∈ F) :
    VertexGeometry.Refines F (isolatePartition S a) := by
  have checks := source_agreement_checks hF
  intro C hC
  by_cases he : C = [a]
  · exact ⟨[a],by simp [isolatePartition],by simpa [he]⟩
  · refine ⟨(leaves S).filter (fun x => x != a),by simp [isolatePartition],?_⟩
    intro x hx
    have hxa : x ≠ a := by
      intro hxa
      exact he (shared_label_block_equal checks.1 checks.2 hC ha (hxa ▸ hx) (by simp))
    simp [block_labels checks.1 hC hx,hxa]

/-- Uniform original rooted Rule4 no-larger cover. This is the consuming graph
safety theorem; it assumes only actual source guards and original agreement.
The no-common/no-t1 priority guards are needed by selection and branch cost,
not silently replaced by a desired coverage premise. -/
theorem actual_rule4_cover {T S : Tree}
    (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
    {a b c : Nat} (hab : a ≠ b) (hcT : HasCherry a b T) (hcS : HasCherry a c S)
    {q r : RMAF.Vertex} (hcuts : (pendantOriginal S a b).Perm [q,r])
    (hql : subtreeLabels S q = [c]) {F : List (List Nat)}
    (hF : agreement T S F = true) :
    ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧
      (VertexGeometry.Refines G (literalThree S q r) ∨
       VertexGeometry.Refines G (isolatePartition S a) ∨
       VertexGeometry.Refines G (pendantPartition T a c)) := by
  by_cases haSingle : [a] ∈ F
  · exact ⟨F,hF,Nat.le_refl _,Or.inr (Or.inl (singleton_refines_isolate hF haSingle))⟩
  obtain ⟨q',r',hcuts',_,_,hcover⟩ := actual_hard2_unordered_safety hnS hF
    (hasCherry_address hcT) (two_cut_length hcuts)
  rcases hcover with haSingle' | hbSingle | hRef
  · exact False.elim (haSingle haSingle')
  · have checks := source_agreement_checks hF
    have hal : a ∈ leaves S := by
      have ht : a ∈ leaves T := (hasCherry_labels hcT).1
      obtain ⟨B,hB,haB⟩ := partitionCheck_covers _ F
        (agreement_parts T S F hF).1 a ht
      exact block_labels checks.1 hB haB
    obtain ⟨B,hB,haB⟩ := partitionCheck_covers _ F checks.1 a hal
    have second : ∃ d, d ∈ B ∧ d ∈ leaves S ∧ d ≠ a := by
      apply Classical.byContradiction
      intro hn
      have only : ∀ d, d ∈ B → d = a := by
        intro d hd
        by_cases he : d = a
        · exact he
        · exact False.elim (hn ⟨d,hd,block_labels checks.1 hB hd,he⟩)
      have he := block_singleton_of_only checks.1 hB haB only
      exact haSingle (by simpa [he] using hB)
    by_cases hcB : c ∈ B
    · exact ⟨F,hF,Nat.le_refl _,Or.inr (Or.inr
        (common_pair_all_pendants hnT (agreement_reverse hF) hcS hB haB hcB))⟩
    · by_cases hd : ∃ d, d ∈ B ∧ d ∈ subtreeLabels S r
      · obtain ⟨G,hG,hlen,hGref⟩ := actual_original_exchange hnT hnS hab hcT hcS hcuts hql hF hB haB hcB hbSingle hd
        exact ⟨G,hG,Nat.le_of_eq hlen,Or.inl hGref⟩
      · have hno : ∀ d, d ∈ B → d ∉ subtreeLabels S r := by intro d hdb hdr; exact hd ⟨d,hdb,hdr⟩
        exact ⟨F,hF,Nat.le_refl _,Or.inl
          (retained_a_block_refines hnS hF hab hcS hcuts hql hB haB hcB hbSingle hno second)⟩
  · exact ⟨F,hF,Nat.le_refl _,Or.inl (refines_two_cut_order hcuts hcuts' hRef)⟩
end Universal233.Rule4
