import Rule4LiteralCuts

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

theorem antichain_labels_disjoint {S : Tree} (hn : (leaves S).Nodup)
    {cuts : List RMAF.Vertex} (h : OriginalAntichain S cuts)
    {q r : RMAF.Vertex} (hq : q ∈ cuts) (hr : r ∈ cuts) (hne : q ≠ r) :
    ∀ x, x ∈ subtreeLabels S q → x ∉ subtreeLabels S r := by
  intro x hx hy
  obtain ⟨u,hu,hup⟩ := (subtreeLabels_prefix S q x).1 hx
  obtain ⟨v,hv,hvp⟩ := (subtreeLabels_prefix S r x).1 hy
  have he := leaf_unique hn hu hv
  rw [he] at hup
  have hi := h.incomparable q r hq hr hne
  rcases List.prefix_or_prefix_of_prefix hup hvp with hh | hh
  · exact hi.1 hh
  · exact hi.2 hh

theorem flatten_nodup_of_parts (P : List (List Nat))
    (hn : ∀ C, C ∈ P → C.Nodup)
    (hd : P.Pairwise (fun C D => ∀ x, x ∈ C → x ∉ D)) : P.flatten.Nodup := by
  induction P with
  | nil => simp
  | cons C P ih =>
    obtain ⟨hCP,hP⟩ := List.pairwise_cons.1 hd
    apply List.nodup_append.2
    refine ⟨hn C (by simp),ih (by intro D hD; exact hn D (by simp [hD])) hP,?_⟩
    intro x hx y hy he
    obtain ⟨D,hD,hyD⟩ := List.mem_flatten.1 hy
    exact hCP D hD x hx (he ▸ hyD)

theorem antichain_partition_checked {S : Tree} (hn : (leaves S).Nodup)
    {cuts : List RMAF.Vertex} (h : OriginalAntichain S cuts) {a : Nat}
    (ha : a ∈ leaves S) (hretain : ∀ q, q ∈ cuts → a ∉ subtreeLabels S q) :
    partitionCheck (leaves S) (literalPartition S cuts) = true := by
  let C := (leaves S).filter (fun x => cuts.all (fun q => !(subtreeLabels S q).contains x))
  have mapped : (cuts.map (subtreeLabels S)).Pairwise (fun A B => ∀ x, x ∈ A → x ∉ B) := by
    apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem ?_ h.distinct
    intro q r hq hr hne
    exact antichain_labels_disjoint hn h hq hr hne
  have labelsPair : (literalPartition S cuts).Pairwise (fun A B => ∀ x, x ∈ A → x ∉ B) := by
    apply List.pairwise_append.2
    refine ⟨mapped,by simp,?_⟩
    intro A hA B hB x hx hxB
    have hBC : B = C := by simpa [C] using hB
    subst B
    obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hA
    have allq := (List.mem_filter.1 hxB).2
    have ho : x ∉ subtreeLabels S q := by simpa using (List.all_eq_true.1 allq) q hq
    exact ho hx
  have allNodup : ∀ A, A ∈ literalPartition S cuts → A.Nodup := by
    intro A hA
    rcases List.mem_append.1 hA with hA | hA
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hA
      exact (subtreeLabels_sublist S q).nodup hn
    · have he : A = C := by simpa [C] using hA
      subst A; exact hn.filter _
  have hflat := flatten_nodup_of_parts _ allNodup labelsPair
  have cover : ∀ x, x ∈ leaves S → x ∈ (literalPartition S cuts).flatten := by
    intro x hx
    by_cases hex : ∃ q, q ∈ cuts ∧ x ∈ subtreeLabels S q
    · obtain ⟨q,hq,hxq⟩ := hex
      exact List.mem_flatten.2 ⟨subtreeLabels S q,List.mem_append_left _ (List.mem_map.2 ⟨q,hq,rfl⟩),hxq⟩
    · have hxc : x ∈ C := by
        apply List.mem_filter.2
        exact ⟨hx,List.all_eq_true.2 (by intro q hq; have hh : x ∉ subtreeLabels S q := fun hm => hex ⟨q,hq,hm⟩; simpa using hh)⟩
      exact List.mem_flatten.2 ⟨C,List.mem_append_right _ (by simp [C]),hxc⟩
  apply partition_intro
  · intro A hA
    rcases List.mem_append.1 hA with hA | hA
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hA
      exact subtreeLabels_nonempty (h.actual q hq)
    · have he : A = C := by simpa [C] using hA
      subst A
      have ham : a ∈ C := by
        apply List.mem_filter.2
        exact ⟨ha,List.all_eq_true.2 (by intro q hq; simpa using hretain q hq)⟩
      intro he; simpa [he] using ham
  · intro x hx
    simpa [cover x hx] using hflat.count (a := x)
  · intro x hx
    obtain ⟨A,hA,hxA⟩ := List.mem_flatten.1 hx
    rcases List.mem_append.1 hA with hA | hA
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hA
      exact (subtreeLabels_sublist S q).subset hxA
    · have he : A = C := by simpa [C] using hA
      subst A
      exact (List.mem_filter.1 hxA).1

theorem antichain_source_embeddings {S : Tree} (hn : (leaves S).Nodup)
    {cuts : List RMAF.Vertex} (h : OriginalAntichain S cuts) :
    pairwiseEmbeddings S (literalPartition S cuts) = true := by
  let C := (leaves S).filter (fun x => cuts.all (fun q => !(subtreeLabels S q).contains x))
  have localClear (q : RMAF.Vertex) (hq : q ∈ cuts) (E : List Nat)
      (hEl : E ⊆ leaves S) (hEo : ∀ x, x ∈ E → x ∉ subtreeLabels S q) :
      Disj S (subtreeLabels S q) E := by
    obtain ⟨U,hU⟩ := h.actual q hq
    have hl := subtreeLabels_eq_leaves hU
    have ht : treeAt S q = some U := by rw [treeAt_eq_subtree]; exact hU
    exact original_clade_clear hn ht (subtreeLabels S q) E
      (subtreeLabels_sublist S q).subset hEl
      (by simpa only [hl] using (show subtreeLabels S q ⊆ subtreeLabels S q from fun _ hx => hx))
      (by simpa only [hl] using hEo)
  apply (executable_pairwiseEmbeddings S _).2
  apply List.pairwise_append.2
  refine ⟨?_,by simp,?_⟩
  · apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem ?_ h.distinct
    intro q r hq hr hne
    exact localClear q hq (subtreeLabels S r) (subtreeLabels_sublist S r).subset
      (by intro x hx; exact antichain_labels_disjoint hn h hr hq (Ne.symm hne) x hx)
  · intro A hA B hB
    have he : B = C := by simpa [C] using hB
    subst B
    obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hA
    exact localClear q hq C (by intro x hx; exact (List.mem_filter.1 hx).1)
      (by intro x hx; simpa using (List.all_eq_true.1 (List.mem_filter.1 hx).2) q hq)
end Universal233.Rule4
