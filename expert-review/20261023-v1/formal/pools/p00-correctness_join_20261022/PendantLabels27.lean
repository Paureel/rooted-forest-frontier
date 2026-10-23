-- Own cut-label separation and partition proof; lower grants are explicit.
import PrefixEndpoint22
import PartitionTools20
open RMAF Universal233 CherryBranching VertexGeometry SourceBoundary OwnHigh
namespace HighChildren
theorem cut_valid (S : Tree) (a b : Nat) (v : List Bool) (hv : v∈cuts S a b) :
    CoreGraph.Valid S v := by
  exact (HardParent.vertices_correct S v).mp (List.mem_filter.mp hv).1
theorem cut_nonempty (S : Tree) (a b : Nat) (v : List Bool) (hv : v∈cuts S a b) :
    HardParent.subtreeLabels S v≠[] := HardParent.subtreeLabels_nonempty (cut_valid S a b v hv)
theorem cut_list_nodup (S : Tree) (a b : Nat) : (cuts S a b).Nodup :=
  (HardParent.vertices_nodup S).filter _
theorem cut_labels_nodup (S : Tree) (v : List Bool) (hn : (leaves S).Nodup) :
    (HardParent.subtreeLabels S v).Nodup := (HardParent.subtreeLabels_sublist S v).nodup hn
theorem cut_labels_disjoint (S : Tree) (a b : Nat) (hn : (leaves S).Nodup)
    (v w : List Bool) (hv : v∈cuts S a b) (hw : w∈cuts S a b) (hne : v≠w)
    (x : Nat) (hx : x∈HardParent.subtreeLabels S v) : x∉HardParent.subtreeLabels S w := by
  intro hy
  obtain ⟨p,hvp,hp⟩ := label_below_has_leaf S v x hx
  obtain ⟨q,hwq,hq⟩ := label_below_has_leaf S w x hy
  have he := leaf_address_unique S x p q hn hp hq
  subst q
  rcases prefix_comparable v w p hvp hwq with hpre | hpre
  · exact hne (cuts_antichain S a b v w hv hw hpre)
  · exact hne (cuts_antichain S a b w v hw hv hpre).symm
theorem mapped_flat_nodup (S : Tree) (V : List (List Bool))
    (hn : V.Nodup) (hlabels : ∀v∈V,(HardParent.subtreeLabels S v).Nodup)
    (hdisj : ∀v∈V,∀w∈V,v≠w → ∀x∈HardParent.subtreeLabels S v,x∉HardParent.subtreeLabels S w) :
    (V.map (HardParent.subtreeLabels S)).flatten.Nodup := by
  induction V with
  | nil => exact List.nodup_nil
  | cons v V ih =>
    have hnd:=List.nodup_cons.mp hn
    simp only [List.map_cons,List.flatten_cons]
    refine List.nodup_append.mpr ⟨hlabels v List.mem_cons_self,?_,?_⟩
    · exact ih hnd.2 (fun w hw=>hlabels w (List.mem_cons_of_mem v hw))
        (fun w hw z hz=>hdisj w (List.mem_cons_of_mem v hw) z (List.mem_cons_of_mem v hz))
    · intro x hx y hy he
      subst y
      obtain ⟨B,hB,hxB⟩:=List.mem_flatten.mp hy
      obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hB
      exact hdisj v List.mem_cons_self w (List.mem_cons_of_mem v hw) (fun he=>hnd.1 (he ▸ hw)) x hx hxB
theorem core_endpoint (S : Tree) (a b : Nat) (ha : a∈leaves S) : a∈coreLabels S a b := by
  apply List.mem_filter.mpr
  refine ⟨ha,?_⟩
  simp only [Bool.not_eq_true']
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨B,hB,haB⟩:=List.mem_flatten.mp (List.contains_iff_mem.mp h)
  obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hB
  have hc:=cut_boundary S a b v hv
  exact frontier_label_absent S [a,b] v hc.1 hc.2 a haB (by simp only [List.mem_cons,List.mem_singleton,true_or])
theorem pendant_partition (S : Tree) (a b : Nat) (hn : (leaves S).Nodup) (ha : a∈leaves S) :
    partitionCheck (leaves S) (pendantPartition S a b)=true := by
  let blocks := (cuts S a b).map (HardParent.subtreeLabels S)
  have hblocks : blocks.flatten.Nodup := mapped_flat_nodup S (cuts S a b) (cut_list_nodup S a b)
    (fun v _=>cut_labels_nodup S v hn) (fun v hv w hw=>cut_labels_disjoint S a b hn v w hv hw)
  have hflat : (pendantPartition S a b).flatten=blocks.flatten++coreLabels S a b := by
    simp only [pendantPartition,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
    rfl
  apply partition_from_flat
  · rw [hflat]
    refine List.nodup_append.mpr ⟨hblocks,hn.filter _,?_⟩
    intro x hx y hy he
    subst y
    have hh := (List.mem_filter.mp hy).2
    simp only [Bool.not_eq_true'] at hh
    exact Bool.noConfusion ((List.contains_iff_mem.mpr hx).symm.trans hh)
  · intro B hB
    rcases List.mem_append.mp hB with hB | hB
    · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hB
      exact cut_nonempty S a b v hv
    · have he := List.mem_singleton.mp hB
      subst B
      intro hn
      have hx:=core_endpoint S a b ha
      rw [hn] at hx
      exact List.not_mem_nil hx
  · intro x
    rw [hflat]
    constructor
    · intro hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨B,hB,hxB⟩:=List.mem_flatten.mp hx
        obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hB
        exact (HardParent.subtreeLabels_sublist S v).subset hxB
      · exact (List.mem_filter.mp hx).1
    · intro hx
      by_cases hb : x∈blocks.flatten
      · exact List.mem_append_left _ hb
      · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hx,by
          simp only [Bool.not_eq_true']
          exact Bool.eq_false_iff.mpr (fun h=>hb (List.contains_iff_mem.mp h))⟩)
end HighChildren
