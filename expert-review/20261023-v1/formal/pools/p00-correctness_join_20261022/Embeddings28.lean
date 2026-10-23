-- Own hull separation for the actual pendant child.
import PendantLabels27
open RMAF Universal233 CherryBranching VertexGeometry SourceBoundary OwnHigh
namespace HighChildren
theorem subtree_minimal_prefix (S : Tree) (P : List Nat) (v w : List Bool)
    (hn : (leaves S).Nodup) (hP : ∀x∈P,x∈HardParent.subtreeLabels S v)
    (hw : w∈minimalVertices P S) : v <+: w := by
  have endpoint : ∀z,selectedLeaves P S z → v <+: z := by
    intro z hz
    obtain ⟨x,hx,hxz⟩:=(selected_leaf_iff P S z).mp hz
    obtain ⟨q,hvq,hq⟩:=label_below_has_leaf S v x (hP x hx)
    have he:=leaf_address_unique S x z q hn hxz hq
    exact he ▸ hvq
  obtain ⟨p,q,hp,hq,hpath⟩:=(minimalVertices_correct P S w).mp hw
  exact path_prefix_closed hpath v (endpoint p hp) (endpoint q hq)
theorem outside_minimal_avoids (S : Tree) (P : List Nat) (v w : List Bool)
    (hP : ∀x∈P,x∉HardParent.subtreeLabels S v)
    (hw : w∈minimalVertices P S) : ¬v <+: w := by
  intro hvw
  obtain ⟨p,q,hp,hq,hpath⟩:=(minimalVertices_correct P S w).mp hw
  obtain ⟨x,hx,hxp⟩:=(selected_leaf_iff P S p).mp hp
  obtain ⟨y,hy,hyq⟩:=(selected_leaf_iff P S q).mp hq
  rcases path_prefix_endpoint hpath v hvw with hpre | hpre
  · exact hP x hx (leaf_below_label S v p x hpre hxp)
  · exact hP y hy (leaf_below_label S v q y hpre hyq)
theorem cut_core_disjoint (S : Tree) (a b : Nat) (v : List Bool)
    (hn : (leaves S).Nodup) :
    disjointVertices (minimalVertices (HardParent.subtreeLabels S v) S)
      (minimalVertices (coreLabels S a b) S)=true ∨ v∉cuts S a b := by
  by_cases hv : v∈cuts S a b
  · left
    simp only [disjointVertices,List.all_eq_true,Bool.not_eq_true']
    intro w hw
    apply Bool.eq_false_iff.mpr
    intro hc
    have hpre:=subtree_minimal_prefix S (HardParent.subtreeLabels S v) v w hn (fun _ hx=>hx) hw
    have havoid : ∀x∈coreLabels S a b,x∉HardParent.subtreeLabels S v := by
      intro x hx hcut
      have hfalse := (List.mem_filter.mp hx).2
      have htrue : ((cuts S a b).map (HardParent.subtreeLabels S)).flatten.contains x=true :=
        List.contains_iff_mem.mpr (List.mem_flatten.mpr ⟨HardParent.subtreeLabels S v,List.mem_map.mpr ⟨v,hv,rfl⟩,hcut⟩)
      simp only [htrue,Bool.not_true] at hfalse
      cases hfalse
    exact outside_minimal_avoids S (coreLabels S a b) v w havoid (List.contains_iff_mem.mp hc) hpre
  · exact Or.inr hv
theorem distinct_cut_minimal_disjoint (S : Tree) (a b : Nat) (v q : List Bool)
    (hn : (leaves S).Nodup) (hv : v∈cuts S a b) (hq : q∈cuts S a b) (hne : v≠q) :
    disjointVertices (minimalVertices (HardParent.subtreeLabels S v) S)
      (minimalVertices (HardParent.subtreeLabels S q) S)=true := by
  simp only [disjointVertices,List.all_eq_true,Bool.not_eq_true']
  intro w hw
  apply Bool.eq_false_iff.mpr
  intro hqW
  have hvw:=subtree_minimal_prefix S (HardParent.subtreeLabels S v) v w hn (fun _ hx=>hx) hw
  have hqw:=subtree_minimal_prefix S (HardParent.subtreeLabels S q) q w hn (fun _ hx=>hx) (List.contains_iff_mem.mp hqW)
  rcases prefix_comparable v q w hvw hqw with hpre | hpre
  · exact hne (cuts_antichain S a b v q hv hq hpre)
  · exact hne (cuts_antichain S a b q v hq hv hpre).symm
theorem block_list_nodup (F : List (List Nat)) (hn : F.flatten.Nodup)
    (hne : ∀P∈F,P≠[]) : F.Nodup := by
  induction F with
  | nil => exact List.nodup_nil
  | cons P F ih =>
    have hnd:=List.nodup_append.mp hn
    apply List.nodup_cons.mpr
    refine ⟨?_,ih hnd.2.1 (fun Q hQ=>hne Q (List.mem_cons_of_mem P hQ))⟩
    intro hP
    obtain ⟨x,hx⟩:=List.exists_mem_of_ne_nil P (hne P List.mem_cons_self)
    exact hnd.2.2 x hx x (List.mem_flatten.mpr ⟨P,hP,hx⟩) rfl
theorem embeddings_of_disjoint (S : Tree) (F : List (List Nat)) (hn : F.Nodup)
    (hdisj : ∀P∈F,∀Q∈F,P≠Q → disjointVertices (minimalVertices P S) (minimalVertices Q S)=true) :
    pairwiseEmbeddings S F=true := by
  induction F with
  | nil => rfl
  | cons P F ih =>
    have hnd:=List.nodup_cons.mp hn
    simp only [pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true]
    refine ⟨?_,ih hnd.2 (fun Q hQ R hR=>hdisj Q (List.mem_cons_of_mem P hQ) R (List.mem_cons_of_mem P hR))⟩
    intro Q hQ
    exact hdisj P List.mem_cons_self Q (List.mem_cons_of_mem P hQ) (fun he=>hnd.1 (he ▸ hQ))
theorem pendant_embeddings (S : Tree) (a b : Nat) (hn : (leaves S).Nodup) (ha : a∈leaves S) :
    pairwiseEmbeddings S (pendantPartition S a b)=true := by
  have hp:=pendant_partition S a b hn ha
  have hne : ∀P∈pendantPartition S a b,P≠[] := by
    have h:=hp
    simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true,Bool.not_eq_true'] at h
    intro P hP he
    have hh:=h.1.1 P hP
    subst P
    cases hh
  apply embeddings_of_disjoint S _ (block_list_nodup _ (partition_flat_nodup _ _ hp) hne)
  intro P hP Q hQ hPQ
  rcases List.mem_append.mp hP with hP | hP
  · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hP
    rcases List.mem_append.mp hQ with hQ | hQ
    · obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hQ
      exact distinct_cut_minimal_disjoint S a b v q hn hv hq (fun he=>hPQ (congrArg (HardParent.subtreeLabels S) he))
    · have he:=List.mem_singleton.mp hQ
      subst Q
      exact (cut_core_disjoint S a b v hn).resolve_right (fun h=>h hv)
  · have he:=List.mem_singleton.mp hP
    subst P
    rcases List.mem_append.mp hQ with hQ | hQ
    · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hQ
      exact disjoint_symm _ _ ((cut_core_disjoint S a b v hn).resolve_right (fun h=>h hv))
    · exact False.elim (hPQ (List.mem_singleton.mp hQ).symm)
end HighChildren
