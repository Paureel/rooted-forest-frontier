import ProjectedPartition
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

def projected (X B : List Nat) (F : List (List Nat)) (y : Nat) :=
  (B.filter (X.contains ·)++[y])::clip X F

theorem projected_embeddings (T : Tree) (X Y B : List Nat) (F : List (List Nat)) (y : Nat)
    (nd : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,Y]=true)
    (edge : OriginalSplit T X Y) (hy : y∈Y) (neY : B.filter (Y.contains ·)≠[])
    (he : pairwiseEmbeddings T (B::F)=true) :
    pairwiseEmbeddings T (projected X B F y)=true := by
  have hparts := he
  simp only [pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true,clear_iff] at hparts
  obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil _ neY
  have hzB := (List.mem_filter.1 hz).1
  have hzY := List.contains_iff_mem.1 (List.mem_filter.1 hz).2
  simp only [projected,pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true,clear_iff]
  refine ⟨?_,clip_embeddings T X F hparts.2⟩
  intro E hE
  obtain ⟨D,hD,hDE,hne⟩ := clip_mem X F E hE
  have subD : E⊆D := by rw [hDE];intro x hx;exact (List.mem_filter.1 hx).1
  have clearBE : Clear (minimalVertices B T) (minimalVertices E T) := by
    intro v hv hw
    exact hparts.1 D hD v hv
      (VertexGeometry.executable_span_monotone T E D (fun _ hx => subD hx) v hw)
  exact original_projection_clear T X Y B (B.filter (X.contains ·)) E y z nd hp edge
    (by intro x hx;exact List.contains_iff_mem.1 (List.mem_filter.1 hx).2)
    (by intro x hx;exact (List.mem_filter.1 hx).1) (clip_sub X F E hE) hy hzY hzB clearBE

theorem projected_topologies (T S : Tree) (X Y B : List Nat) (F : List (List Nat)) (y m : Nat)
    (ndT : (leaves T).Nodup) (ndS : (leaves S).Nodup)
    (hpT : partitionCheck (leaves T) [X,Y]=true) (hpS : partitionCheck (leaves S) [X,Y]=true)
    (edgeT : OriginalSplit T X Y) (edgeS : OriginalSplit S X Y)
    (neX : B.filter (X.contains ·)≠[]) (neY : B.filter (Y.contains ·)≠[])
    (hy : y∈Y) (freshT : m∉leaves T) (freshS : m∉leaves S)
    (ha : agreement T S (B::F)=true) :
    ∀E∈projected X B F y,restrictionAgrees T S E=true := by
  have hh := ha
  simp only [agreement,Bool.and_eq_true] at hh
  intro E hE
  rcases List.mem_cons.1 hE with rfl | hE
  · exact original_crossing_topology T S X Y B y m ndT ndS hpT hpS edgeT edgeS
      (fun _ hx => checked_label _ _ hh.1.1.1.1 (by simp) hx)
      (fun _ hx => checked_label _ _ hh.1.1.1.2 (by simp) hx)
      neX neY hy freshT freshS (List.all_eq_true.1 hh.1.1.2 B (by simp))
  · obtain ⟨D,hD,hDE,hne⟩ := clip_mem X F E hE
    have subD : E⊆D := by rw [hDE];intro x hx;exact (List.mem_filter.1 hx).1
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil E hne
    exact BinaryExchange.restrictionAgrees_sub T S D E
      (List.all_eq_true.1 hh.1.1.2 D (List.mem_cons_of_mem B hD)) (fun _ h => subD h)
      ⟨x,hx,checked_label _ _ hh.1.1.1.1 (List.mem_cons_of_mem B hD) (subD hx)⟩

/-- Assemble a family on a literal restriction from its original-address
checks. This helper does not supply the checks; the projection theorems above
derive topology and both embeddings from the original agreement. -/
theorem family_restrict_agrees (T S t s : Tree) (U : List Nat) (G : List (List Nat))
    (ht : restrict U T=some t) (hs : restrict U S=some s)
    (lt : (leaves t).Perm U) (ls : (leaves s).Perm U)
    (hp : partitionCheck U G=true)
    (et : pairwiseEmbeddings T G=true) (es : pairwiseEmbeddings S G=true)
    (topo : ∀B∈G,restrictionAgrees T S B=true) : agreement t s G=true := by
  have sub : ∀B∈G,B⊆U := fun B hB _ hx => checked_label U G hp hB hx
  simp only [agreement,Bool.and_eq_true]
  refine ⟨⟨⟨⟨(partition_labels_congr (leaves t) U G (fun _ => lt.mem_iff)).2 hp,
    (partition_labels_congr (leaves s) U G (fun _ => ls.mem_iff)).2 hp⟩,?_⟩,
    (pairwise_transport T t U G ht sub).1 et⟩,(pairwise_transport S s U G hs sub).1 es⟩
  apply List.all_eq_true.2
  intro B hB
  rw [sameShape_restrict_inside T S t s U B ht hs (sub B hB)]
  exact topo B hB

end OrdinaryCommonSplit
