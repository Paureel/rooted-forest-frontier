-- Own source boundary proof, then the literal frozen dichotomy.
import Addresses14
open RMAF Universal233 VertexGeometry OwnHigh
namespace SourceBoundary
theorem cut_boundary (S : Tree) (a b : Nat) (v : List Bool)
    (hv : v ∈ CherryBranching.cuts S a b) :
    v.dropLast ∈ minimalVertices [a,b] S ∧ v ∉ minimalVertices [a,b] S := by
  unfold CherryBranching.cuts HardParent.pendantOriginal at hv
  have h := (List.mem_filter.mp hv).2
  simp only [Bool.and_eq_true] at h
  refine ⟨List.contains_iff_mem.mp h.1.2,?_⟩
  intro hmem
  simp at h
  exact h.2 hmem
theorem shared_block_avoids_pendants (S U : Tree) (P : List Nat) (a b : Nat)
    (hn : (leaves S).Nodup) (hr : restrict P S = some U) (hc : HasCherry U a b) :
    ∀ v ∈ CherryBranching.cuts S a b, ∀ x ∈ HardParent.subtreeLabels S v, x ∉ P := by
  obtain ⟨r,V,hV,hlabels⟩ := selected_cluster S U P a b hr hc
  have hprefix : ∀ z, selectedLeaves [a,b] S z → r <+: z := by
    intro z hz
    obtain ⟨x,hx,hxz⟩ := (selected_leaf_iff [a,b] S z).mp hz
    have hpair : x=a ∨ x=b := by simpa using hx
    have hxV := ((hlabels x).mpr hpair).1
    exact leaf_cluster_prefix S V r z x hn hV hxV hxz
  intro v hv x hx hPx
  obtain ⟨hw,hnot⟩ := cut_boundary S a b v hv
  have hrw : r <+: v.dropLast := by
    obtain ⟨z,z',hz,hz',hpath⟩ := (minimalVertices_correct [a,b] S v.dropLast).mp hw
    exact path_prefix_closed hpath r (hprefix z hz) (hprefix z' hz')
  have hrv : r <+: v := hrw.trans (List.dropLast_prefix v)
  obtain ⟨z,hvz,hz⟩ := label_below_has_leaf S v x hx
  have hxR := leaf_below_label S r z x (hrv.trans hvz) hz
  have hxV : x ∈ leaves V := by simpa [subtree_labels_eq,hV] using hxR
  have hpair := (hlabels x).mp ⟨hxV,hPx⟩
  have hxD : x ∈ [a,b] := by simpa using hpair
  exact frontier_label_absent S [a,b] v hw hnot x hx hxD
theorem source_no_crossing (S : Tree) (a b : Nat) (F : List (List Nat)) (P : List Nat)
    (hn : (leaves S).Nodup) (hpart : partitionCheck (leaves S) F = true)
    (hemb : pairwiseEmbeddings S F = true) (hp : P ∈ F) (ha : a ∈ P) (hb : b ∈ P)
    (hres : ∃ U, restrict P S = some U ∧ HasCherry U a b) : NoPendantCrossing S a b F := by
  obtain ⟨U,hr,hc⟩ := hres
  have havoid := shared_block_avoids_pendants S U P a b hn hr hc
  intro v hv Q hQ x hxQ hxCut
  by_cases hQP : Q=P
  · subst Q
    exact False.elim (havoid v hv x hxCut hxQ)
  · intro y hy
    apply Classical.byContradiction
    intro hyOut
    obtain ⟨hw,hnot⟩ := cut_boundary S a b v hv
    obtain ⟨z,hvz,hz⟩ := label_below_has_leaf S v x hxCut
    have hyS := block_subset (leaves S) F hpart Q hQ y hy
    obtain ⟨z',hz'⟩ := label_has_leaf S y hyS
    have hvz' : ¬ v <+: z' := by
      intro hpre
      exact hyOut (leaf_below_label S v z' y hpre hz')
    have hpath := parent_separates v z z' hvz hvz'
    have hQz : selectedLeaves Q S z := (selected_leaf_iff Q S z).mpr ⟨x,hxQ,hz⟩
    have hQz' : selectedLeaves Q S z' := (selected_leaf_iff Q S z').mpr ⟨y,hy,hz'⟩
    have hwQ : v.dropLast ∈ minimalVertices Q S :=
      (minimalVertices_correct Q S v.dropLast).mpr ⟨z,z',hQz,hQz',hpath⟩
    have hsub : ∀ t ∈ ([a,b] : List Nat), t ∈ P := by
      intro t ht
      have ht' : t=a ∨ t=b := by simpa using ht
      rcases ht' with rfl | rfl
      · exact ha
      · exact hb
    have hwP := executable_span_monotone S [a,b] P hsub v.dropLast hw
    have hne : P≠Q := fun he => hQP he.symm
    have hd := disjoint_pair S F P Q hemb hp hQ hne
    have hd' : ∀ w ∈ minimalVertices P S, (minimalVertices Q S).contains w = false := by
      simpa only [disjointVertices,List.all_eq_true,Bool.not_eq_true'] using hd
    have hfalse := hd' v.dropLast hwP
    have htrue : (minimalVertices Q S).contains v.dropLast = true := List.contains_iff_mem.mpr hwQ
    exact Bool.noConfusion (htrue.symm.trans hfalse)
theorem source_boundary : SourceBoundaryObligation := by
  intro S a b F P hn hab hpart hemb hp ha hb hres
  exact source_no_crossing S a b F P hn hpart hemb hp ha hb hres
theorem literal_dichotomy (T S : Tree) (p : RMAF.Vertex) (a b : Nat) (F : List (List Nat))
    (hproper : DepthOne.proper T S = true) (hc : CoreGraph.CherryAt T p a b)
    (hag : agreement T S F = true) :
    [a] ∈ F ∨ [b] ∈ F ∨ VertexGeometry.Refines F (CherryBranching.pendantPartition S a b) := by
  exact literal_consumer source_boundary T S p a b F hproper hc hag
#print axioms source_boundary
#print axioms literal_dichotomy
#check source_boundary
#check literal_dichotomy
end SourceBoundary
