import Surgery
namespace BinaryExchange
open RMAF VertexGeometry

theorem mixed_occupies (t u : Tree) (v : RMAF.Vertex) (C : List Nat)
    (hn : (leaves t).Nodup) (he : treeAt t v = some u)
    (hC : Sub C (leaves t)) (hm : mixed C ((leaves u).contains ·) = true) :
    v ∈ minimalVertices C t := by
  obtain ⟨⟨x,hx,hqx⟩,⟨y,hy,hqy⟩⟩ := (mixed_iff C _).1 hm
  apply crossing_occupies t u v C hn he hC
  exact ⟨⟨x,hx,List.contains_iff_mem.1 hqx⟩,
    ⟨y,hy,by simpa using hqy⟩⟩

theorem mixed_blocks_at_most_one (t u : Tree) (v : RMAF.Vertex) (V : List (List Nat))
    (hn : (leaves t).Nodup) (he : treeAt t v = some u)
    (hV : V.Pairwise (Disj t)) (hl : ∀ C, C ∈ V → Sub C (leaves t)) :
    (V.filter (mixed · ((leaves u).contains ·))).length ≤ 1 := by
  apply marked_at_most_one V _ (Disj t) hV
  intro C hC E hE hd hmC hmE
  have hc := mixed_occupies t u v C hn he (hl C hC) hmC
  have he' := mixed_occupies t u v E hn he (hl E hE) hmE
  exact hd v ⟨(minimalVertices_correct C t v).1 hc,(minimalVertices_correct E t v).1 he'⟩

/-- One possible extra B split is paid by merging at least two A blocks.
This is ownership/count arithmetic on actual original embeddings. -/
theorem exchange_size (s t u : Tree) (v : RMAF.Vertex) (A : List Nat)
    (U V W : List (List Nat))
    (hn : (leaves t).Nodup) (he : treeAt t v = some u)
    (hU : partitionCheck A U = true)
    (hF : agreement s t (U ++ V ++ W) = true)
    (hAm : mixed A ((leaves u).contains ·) = true) :
    (output A V W ((leaves u).contains ·)).length ≤ (U ++ V ++ W).length := by
  let q : Nat → Bool := fun x => (leaves u).contains x
  change (output A V W q).length ≤ (U ++ V ++ W).length
  obtain ⟨hps,hpt,hshape,hpairS,hpairT⟩ := agreement_parts s t _ hF
  obtain ⟨hUV,hW,hUVW⟩ := List.pairwise_append.1 hpairT
  obtain ⟨hUp,hVp,hUVp⟩ := List.pairwise_append.1 hUV
  have hVl : ∀ C, C ∈ V → Sub C (leaves t) := by
    intro C hC; exact partition_sub (leaves t) _ hpt C (by simp [hC])
  have hsl := splitAll_length V q
  have hmone := mixed_blocks_at_most_one t u v V hn he hVp hVl
  change (V.filter (mixed · q)).length ≤ 1 at hmone
  obtain ⟨⟨x,hx,hqx⟩,⟨y,hy,hqy⟩⟩ := (mixed_iff A q).1 hAm
  obtain ⟨D,hD,hxD⟩ := List.mem_flatten.1 ((partition_mem A U hU x).2 hx)
  obtain ⟨E,hE,hyE⟩ := List.mem_flatten.1 ((partition_mem A U hU y).2 hy)
  have hUone : 1 ≤ U.length := by cases U with
    | nil => simp at hD
    | cons C U => simp
  by_cases hcross : ∃ C, C ∈ V ∧ mixed C q = true
  · obtain ⟨C,hC,hmC⟩ := hcross
    have hc := mixed_occupies t u v C hn he (hVl C hC) hmC
    have hDE : D ≠ E := by
      intro hDE
      subst E
      have hmD : mixed D q = true := (mixed_iff D q).2 ⟨⟨x,hxD,hqx⟩,⟨y,hyE,hqy⟩⟩
      have hDl : Sub D (leaves t) := partition_sub (leaves t) _ hpt D (by simp [hD])
      have hd := mixed_occupies t u v D hn he hDl hmD
      exact hUVp D hD C hC v ⟨(minimalVertices_correct D t v).1 hd,(minimalVertices_correct C t v).1 hc⟩
    have hUtwo := two_members_length U D E hD hE hDE
    simp only [output,List.length_cons,List.length_append]
    omega
  · have hmzero : V.filter (mixed · q) = [] := by
      cases hvf : V.filter (mixed · q) with
      | nil => rfl
      | cons C Cs =>
        have hc : C ∈ V.filter (mixed · q) := by simp [hvf]
        exact False.elim (hcross ⟨C,List.mem_filter.1 hc⟩)
    simp only [hmzero,List.length_nil,Nat.add_zero] at hsl
    simp only [output,List.length_cons,List.length_append]
    omega
end BinaryExchange
