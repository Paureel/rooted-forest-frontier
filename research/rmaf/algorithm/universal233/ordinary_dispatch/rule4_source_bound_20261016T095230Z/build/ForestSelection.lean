import ForestProgram
namespace GenericForest
open RMAF RestrictionBridge ForestState OutputState ForestGroups VertexGeometry

theorem split_at_source (ss : List Tree) (i : Nat) (s : Tree) (hi : ss[i]? = some s) :
    ss.take i ++ [s] ++ ss.drop (i+1) = ss := by
  obtain ⟨hlt,he⟩ := List.getElem?_eq_some_iff.1 hi
  have hd := List.drop_eq_getElem_cons hlt
  rw [he] at hd
  have ht := List.take_append_drop i ss
  rw [hd] at ht
  simpa [List.append_assoc] using ht

theorem replace_at_source (ss : List Tree) (i : Nat) (s : Tree) (Q : Forest)
    (hi : ss[i]? = some s) : replace ss i Q = replaced (ss.take i) s (ss.drop (i+1)) Q := by
  simp [replace,hi,replaced]

theorem overlap_selected (t : Tree) (ss : List Tree) (h : Overlap)
    (hh : overlap t ss = some h) :
    ∃ s r, ss[h.left]? = some s ∧ ss[h.right]? = some r ∧ h.left < h.right ∧
      h.vertex ∈ minimalVertices (leaves s) t ∧ h.vertex ∈ minimalVertices (leaves r) t := by
  have hm := List.mem_of_mem_head? (show h ∈ _ from hh)
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.1 hm
  obtain ⟨b,hb,hm⟩ := List.mem_filterMap.1 hm
  split at hm
  · rename_i hab
    obtain ⟨v,hv,he⟩ := Option.map_eq_some_iff.1 hm
    cases he
    obtain ⟨_,hial,hsa⟩ := List.mem_zipIdx ha
    obtain ⟨_,hjbl,hsb⟩ := List.mem_zipIdx hb
    have hia : a.2 < ss.length := by simpa using hial
    have hjb : b.2 < ss.length := by simpa using hjbl
    have hsa' : a.1 = ss[a.2] := by simpa using hsa
    have hsb' : b.1 = ss[b.2] := by simpa using hsb
    refine ⟨a.1,b.1,?_,?_,hab,List.mem_of_find?_eq_some hv,?_⟩
    · simpa only [hsa'] using List.getElem?_eq_getElem hia
    · simpa only [hsb'] using List.getElem?_eq_getElem hjb
    · exact List.contains_iff_mem.1 (List.find?_some hv)
  · simp at hm

theorem selected_parents_distinct (t : Tree) (ss : List Tree)
    (hp : proper (some t) ss = true) (h : Overlap) (hh : overlap t ss = some h) :
    ∃ s r, ss[h.left]? = some s ∧ ss[h.right]? = some r ∧ s ≠ r ∧
      h.vertex ∈ minimalVertices (leaves s) t ∧ h.vertex ∈ minimalVertices (leaves r) t := by
  obtain ⟨s,r,hi,hj,hlt,hv,hw⟩ := overlap_selected t ss h hh
  refine ⟨s,r,hi,hj,?_,hv,hw⟩
  intro he
  obtain ⟨hil,_⟩ := List.getElem?_eq_some_iff.1 hi
  have hij : h.left = h.right := (proper_sources_nodup t ss hp).eq_of_getElem?_eq hil (by simp [he,hi,hj])
  omega

theorem no_overlap_clear (t : Tree) (ss : List Tree) (hh : overlap t ss = none) :
    pairwiseEmbeddings t (ss.map leaves) = true := by
  apply (pairwise_iff t _).2
  rw [List.pairwise_map]
  apply List.pairwise_iff_getElem.2
  intro i j hi hj hij v hv hw
  let a := ss[i]
  let b := ss[j]
  have hai : (a,i) ∈ ss.zipIdx := List.mk_mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hi)
  have hbj : (b,j) ∈ ss.zipIdx := List.mk_mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hj)
  cases hf : (minimalVertices (leaves a) t).find? (fun w => (minimalVertices (leaves b) t).contains w) with
  | none =>
    have hn := List.find?_eq_none.1 hf v hv
    exact hn (List.contains_iff_mem.2 hw)
  | some w =>
    have hm : (⟨i,j,w⟩ : Overlap) ∈ ((ss.zipIdx).flatMap fun a => (ss.zipIdx).filterMap fun b =>
        if a.2 < b.2 then ((minimalVertices (leaves a.1) t).find? fun v =>
          (minimalVertices (leaves b.1) t).contains v).map (Overlap.mk a.2 b.2) else none) := by
      apply List.mem_flatMap.2
      refine ⟨(a,i),hai,List.mem_filterMap.2 ⟨(b,j),hbj,?_⟩⟩
      simp only [hij,ite_true,hf,Option.map_some]
    have hn := List.head?_eq_none_iff.1 hh
    rw [hn] at hm
    exact List.not_mem_nil hm

theorem overlap_child_covers (t : Tree) (ss : List Tree) (F : Forest)
    (ha : agrees (some t) ss F = true) (h : Overlap) (hh : overlap t ss = some h)
    (q : Nat) (hq : additionalCost ss F ≤ q) :
    ∃ i o, (i,o) ∈ branches t ss h q ∧ 1 ≤ o.sourceCuts.length ∧ o.sourceCuts.length ≤ q ∧
      agrees (some t) (replace ss i o.partition) F = true ∧
      additionalCost ss F = o.sourceCuts.length + additionalCost (replace ss i o.partition) F ∧
      additionalCost (replace ss i o.partition) F ≤ q-o.sourceCuts.length := by
  have hp := (agrees_parts _ _ _ ha).1
  obtain ⟨s,r,hi,hj,hne,hv,hw⟩ := selected_parents_distinct t ss hp h hh
  have hs : s ∈ ss := List.mem_of_getElem? hi
  have hr : r ∈ ss := List.mem_of_getElem? hj
  have hn := actual_parent_regions t ss hp s r hs hr hne h.vertex hv hw
  have one (i : Nat) (s : Tree) (hi : ss[i]? = some s)
      (nonlabel : ¬selectedLeaves (leaves s) t h.vertex)
      (occupied : h.vertex ∈ minimalVertices (leaves s) t)
      (clear : Clears t (family (leaves s) F) h.vertex)
      (mem : ∀ o ∈ (Universal233.CoreProgram.generate s (colorLabel t h.vertex) q).outputs,
        (i,o) ∈ branches t ss h q) :
      ∃ i o, (i,o) ∈ branches t ss h q ∧ 1 ≤ o.sourceCuts.length ∧ o.sourceCuts.length ≤ q ∧
        agrees (some t) (replace ss i o.partition) F = true ∧
        additionalCost ss F = o.sourceCuts.length + additionalCost (replace ss i o.partition) F ∧
        additionalCost (replace ss i o.partition) F ≤ q-o.sourceCuts.length := by
    have split := split_at_source ss i s hi
    obtain ⟨o,ho,hnew,hcost,hbudget,hres⟩ := clearing_component_coverage t (ss.take i) s (ss.drop (i+1))
      F (by simpa [split] using ha) h.vertex nonlabel clear q (by simpa [split] using hq)
    have he := replace_at_source ss i s o.partition hi
    exact ⟨i,o,mem o ho,core_emission_positive t ss hp s (List.mem_of_getElem? hi)
      h.vertex nonlabel occupied q o ho,hbudget,by simpa [he] using hnew,
      by simpa [he,split] using hcost,by simpa [he] using hres⟩
  rcases state_two_parent_ownership t ss F ha s r hs hr hne h.vertex with hc | hc
  · apply one h.left s hi hn.1 hv hc
    intro o ho
    simp only [branches,List.mem_append,List.mem_map]
    exact Or.inl ⟨o,by simpa [raw,hi] using ho,rfl⟩
  · apply one h.right r hj hn.2.1 hw hc
    intro o ho
    simp only [branches,List.mem_append,List.mem_map]
    exact Or.inr ⟨o,by simpa [raw,hj] using ho,rfl⟩

end GenericForest
