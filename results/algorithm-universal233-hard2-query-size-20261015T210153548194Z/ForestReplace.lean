import ForestPrecontrols
import SourceValidity
namespace GenericForest
open RMAF RestrictionBridge ForestState OutputState ForestGroups VertexGeometry
open Universal233 Universal233.CoreProgram Universal233.Assembly Universal233.CutRealization

def replaced (pre : List Tree) (s : Tree) (post : List Tree) (Q : Forest) :=
  pre ++ sourceForest s Q ++ post

theorem proper_source_labels (t : Tree) (ss : List Tree)
    (hp : proper (some t) ss = true) (s : Tree) (hs : s ∈ ss) :
    (leaves s).Nodup ∧ leaves s ⊆ leaves t := by
  have hsp := (proper_parts _ _ hp).2
  have hm : leaves s ∈ ss.map leaves := List.mem_map.2 ⟨s,hs,rfl⟩
  exact ⟨RestrictionBridge.checked_block_nodup _ _ hsp _ hm,
    fun _ hx => checked_label _ _ hsp hm hx⟩

theorem proper_replaced (t : Tree) (pre : List Tree) (s : Tree) (post : List Tree)
    (hp : proper (some t) (pre ++ [s] ++ post) = true)
    (hQ : partitionCheck (leaves s) Q = true) :
    proper (some t) (replaced pre s post Q) = true := by
  have hs : s ∈ pre ++ [s] ++ post := by simp
  have hsn := (proper_source_labels t _ hp s hs).1
  have mat := checked_materialization s Q hsn hQ
  have loc := mat.2.1.trans (checked_flatten_perm (leaves s) Q hsn hQ)
  have flat : (((replaced pre s post Q).map leaves).flatten).Perm
      (((pre ++ [s] ++ post).map leaves).flatten) := by
    simp only [replaced,List.map_append,List.map_cons,List.map_nil,List.flatten_append,
      List.flatten_cons,List.flatten_nil,List.append_nil]
    exact ((List.Perm.refl _).append loc).append (List.Perm.refl _)
  obtain ⟨ht,hpart⟩ := proper_parts _ _ hp
  simp only [proper,labels,Bool.and_eq_true]
  refine ⟨decide_eq_true ht,?_⟩
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true] at hpart ⊢
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB
    obtain ⟨u,hu,rfl⟩ := List.mem_map.1 hB
    simpa using RestrictionBridge.leaves_nonempty u
  · intro x hx
    rw [flat.count_eq x]
    exact hpart.1.2 x hx
  · intro x hx
    exact hpart.2 x (flat.mem_iff.1 hx)

theorem source_check_forward (t s : Tree) (Q F : Forest)
    (hsn : (leaves s).Nodup) (hQ : partitionCheck (leaves s) Q = true)
    (hc : sourceCheck (some t) F s = true)
    (href : RestrictionBridge.Refines (family (leaves s) F) Q) :
    ∀ u ∈ sourceForest s Q, sourceCheck (some t) F u = true := by
  simp only [sourceCheck,Bool.and_eq_true] at hc
  intro u hu
  obtain ⟨U,hU,hr⟩ := (source_component s Q u).1 hu
  have hl := component_labels s u U Q hr hsn hQ hU
  have hUs : U ⊆ leaves s := fun _ hx => checked_label _ _ hQ hU hx
  have hf : family (leaves u) F = family U (family (leaves s) F) := by
    rw [family_members (leaves u) U F (fun _ => hl.mem_iff),family_nested U (leaves s) F hUs]
  simp only [sourceCheck,hf,Bool.and_eq_true]
  refine ⟨⟨local_partition s u U (family (leaves s) F) Q hr hc.1.1 hQ href hU,?_⟩,?_⟩
  · apply List.all_eq_true.2
    intro B hB
    obtain ⟨hBG,hBU⟩ := (mem_family _ _ _).1 hB
    rw [source_topology t s u U B hr hBU]
    exact List.all_eq_true.1 hc.1.2 B hBG
  · exact (pairwise_transport s u U _ hr
      (fun B hB => ((mem_family _ _ _).1 hB).2)).1
      (pairwise_filter s (family (leaves s) F) (contained · U) hc.2)

theorem replacement_forward (t : Tree) (pre : List Tree) (s : Tree) (post : List Tree)
    (Q F : Forest) (ha : agrees (some t) (pre ++ [s] ++ post) F = true)
    (hQ : partitionCheck (leaves s) Q = true)
    (href : RestrictionBridge.Refines (family (leaves s) F) Q) :
    agrees (some t) (replaced pre s post Q) F = true := by
  obtain ⟨hp,hF,hown,hE,hS⟩ := agrees_parts _ _ _ ha
  have hs : s ∈ pre ++ [s] ++ post := by simp
  have hsn := (proper_source_labels t _ hp s hs).1
  simp only [agrees,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,contained_iff]
  refine ⟨⟨⟨⟨proper_replaced t pre s post hp hQ,hF⟩,?_⟩,hE⟩,?_⟩
  · intro B hB
    obtain ⟨r,hr,hBr⟩ := hown B hB
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with (hr | rfl) | hr
    · exact ⟨r,by simp [replaced,hr],hBr⟩
    · obtain ⟨U,hU,hBU⟩ := href B ((mem_family _ _ _).2 ⟨hB,hBr⟩)
      obtain ⟨u,hu,hl⟩ := checked_restrictions r Q hsn hQ U hU
      exact ⟨u,by simp [replaced,(source_component r Q u).2 ⟨U,hU,hu⟩],
        fun _ hx => hl.mem_iff.2 (hBU hx)⟩
    · exact ⟨r,by simp [replaced,hr],hBr⟩
  · intro r hr
    simp only [replaced,List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hS r (by simp [hr])
    · exact source_check_forward t s Q F hsn hQ (hS s hs) href r hr
    · exact hS r (by simp [hr])

theorem emitted_replacement_length (pre : List Tree) (s : Tree) (post : List Tree)
    (color : Nat → Nat) (q : Nat) (o : Output) (ho : o ∈ (generate s color q).outputs) :
    (replaced pre s post o.partition).length = (pre ++ [s] ++ post).length + o.sourceCuts.length := by
  have hQ := (generated_source_valid s color q o ho).1
  have hn : (leaves s).Nodup := by
    unfold generate at ho
    split at ho
    · assumption
    · simp at ho
  have hm := (checked_materialization s o.partition hn hQ).1
  obtain ⟨_,_,cs,_,_,_,_,_,_,_,hc⟩ := generate_original_realization s color q o ho
  simp only [replaced,List.length_append,List.length_singleton]
  omega

theorem emitted_replacement_cost (t : Tree) (pre : List Tree) (s : Tree) (post : List Tree)
    (color : Nat → Nat) (q : Nat) (o : Output) (ho : o ∈ (generate s color q).outputs)
    (F : Forest) (ha : agrees (some t) (replaced pre s post o.partition) F = true) :
    additionalCost (pre ++ [s] ++ post) F =
      o.sourceCuts.length + additionalCost (replaced pre s post o.partition) F := by
  have hn := sources_le_blocks _ _ _ ha
  have he := emitted_replacement_length pre s post color q o ho
  simp only [additionalCost]
  omega

end GenericForest
