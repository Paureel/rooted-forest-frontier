import CutHull
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge VertexGeometry PairGeometry

def merged (K L : List Nat) (FX FY : List (List Nat)) := (K++L)::(FX++FY)

theorem merge_partition (labels K L : List Nat) (FX FY : List (List Nat))
    (hp : partitionCheck labels ((K::FX)++(L::FY))=true) :
    partitionCheck labels (merged K L FX FY)=true := by
  obtain ⟨hne,hcount,hlabels⟩ := BinaryExchange.partition_parts labels _ hp
  have hc : ∀x,(merged K L FX FY).flatten.count x=((K::FX)++(L::FY)).flatten.count x := by
    intro x
    simp only [merged,List.flatten_cons,List.flatten_append,List.count_append]
    omega
  apply BinaryExchange.partition_intro
  · intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · have hnK := hne K (by simp)
      exact fun h => hnK (List.append_eq_nil_iff.1 h).1
    · exact hne B (by simpa only [List.mem_append,List.mem_cons] using
        (List.mem_append.1 hB).elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h)))
  · intro x hx;rw [hc];exact hcount x hx
  · intro x hx
    apply hlabels x
    apply List.count_pos_iff.1
    rw [←hc]
    exact List.count_pos_iff.2 hx

theorem merge_embeddings (t : Tree) (K L : List Nat) (FX FY : List (List Nat))
    (x y : Nat) (p : RMAF.Vertex) (b inside : Bool)
    (nd : (leaves t).Nodup) (hxl : x∈leaves t) (hyl : y∈leaves t)
    (hcat : pairwiseEmbeddings t ((K::FX)++(L::FY))=true)
    (hmX : pairwiseEmbeddings t ((K++[y])::FX)=true)
    (hmY : pairwiseEmbeddings t ((L++[x])::FY)=true)
    (hK : ∀a,selectedLeaves K t a→IsSide p b inside a)
    (hL : ∀a,selectedLeaves L t a→IsSide p b (!inside) a)
    (hFX : ∀E∈FX,∀a,selectedLeaves E t a→IsSide p b inside a)
    (hFY : ∀E∈FY,∀a,selectedLeaves E t a→IsSide p b (!inside) a)
    (hy : ∀a,selectedLeaves [y] t a→IsSide p b (!inside) a)
    (hx : ∀a,selectedLeaves [x] t a→IsSide p b inside a) :
    pairwiseEmbeddings t (merged K L FX FY)=true := by
  have htail : pairwiseEmbeddings t (FX++FY)=true := by
    apply (pairwise_iff t _).2
    exact List.Pairwise.sublist
      ((List.sublist_cons_self K FX).append (List.sublist_cons_self L FY))
      ((pairwise_iff t _).1 hcat)
  have cX : ∀E∈FX,Clear (minimalVertices (K++[y]) t) (minimalVertices E t) := by
    have h := hmX
    simp only [pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true,clear_iff] at h
    exact h.1
  have cY : ∀E∈FY,Clear (minimalVertices (L++[x]) t) (minimalVertices E t) := by
    have h := hmY
    simp only [pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true,clear_iff] at h
    exact h.1
  simp only [merged,pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true,clear_iff]
  refine ⟨?_,htail⟩
  intro E hE
  rcases List.mem_append.1 hE with hE | hE
  · exact original_merge_clear t K L E y p b inside nd hyl hK hL (hFX E hE) hy (cX E hE)
  · have hr := original_merge_clear t L K E x p b (!inside) nd hxl hL
      (by simpa using hK) (hFY E hE) (by simpa using hx) (cY E hE)
    have hm : minimalVertices (K++L) t=minimalVertices (L++K) t :=
      Universal233.DepthOne.minimal_members t _ _
        (by intro z;simp only [List.mem_append];exact or_comm)
    rw [hm]
    exact hr

/-- Final checker assembly helper ONLY. Its merged embedding premises remain
explicit and must be discharged by merge_embeddings; merged topology must be
discharged by actual port gluing. This helper alone proves no graph safety or
minimum formula. -/
theorem original_forest_merge_of_checked_embeddings (T S : Tree) (K L : List Nat) (FX FY : List (List Nat))
    (hcat : agreement T S ((K::FX)++(L::FY))=true)
    (htopo : restrictionAgrees T S (K++L)=true)
    (embT : pairwiseEmbeddings T (merged K L FX FY)=true)
    (embS : pairwiseEmbeddings S (merged K L FX FY)=true) :
    agreement T S (merged K L FX FY)=true ∧
      (merged K L FX FY).length+1=((K::FX)++(L::FY)).length := by
  have hh := hcat
  simp only [agreement,Bool.and_eq_true] at hh
  refine ⟨?_,?_⟩
  · simp only [agreement,Bool.and_eq_true]
    refine ⟨⟨⟨⟨merge_partition _ K L FX FY hh.1.1.1.1,
      merge_partition _ K L FX FY hh.1.1.1.2⟩,?_⟩,embT⟩,embS⟩
    apply List.all_eq_true.2
    intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · exact htopo
    · apply List.all_eq_true.1 hh.1.1.2 B
      rcases List.mem_append.1 hB with hB | hB <;> simp [hB]
  · simp [merged,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
end OrdinaryCommonSplit
