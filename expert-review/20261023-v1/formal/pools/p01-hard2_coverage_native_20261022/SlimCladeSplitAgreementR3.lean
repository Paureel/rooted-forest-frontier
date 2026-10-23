/- Reused own frozen proof body; slim import slice, permanently CONTACTED. -/
/- Contacted prover: full original-vertex agreement under a source-clade split. -/
import SlimCleanRestrictionV2R3
open RMAF ForestState Universal233 Universal233.HardParent
open IndependentGeometry IndependentOneExchange
namespace ContactedClade

theorem clean_hulls_disjoint (T : Tree) {A D : List Nat} (cl : Clean A D T) :
 disjointVertices (minimalVertices A T) (minimalVertices D T)=true := by
 apply List.all_eq_true.2
 intro v hv
 have no : v∉minimalVertices D T := by
  intro hd
  exact clean_span_disjoint T cl v hv (minimal_in_span T D v hd)
 simpa using no

theorem target_clade_split_disjoint {T S U : Tree} {p : Vertex}
 (sub : CoreGraph.subtree S p=some U) (nd : (leaves S).Nodup)
 (B : List Nat) (shape : restrictionAgrees T S B=true) :
 disjointVertices (minimalVertices (B.filter (leaves U).contains) T)
  (minimalVertices (B.filter (fun x=>!(leaves U).contains x)) T)=true := by
 have inside : ∀x∈B.filter (leaves U).contains,x∈leaves U := by
  intro x hx;exact List.contains_iff_mem.1 (List.mem_filter.1 hx).2
 have outside : Absent U (B.filter (fun x=>!(leaves U).contains x)) := by
  intro x hx hd
  have no : x∉leaves U := by simpa using (List.mem_filter.1 hd).2
  exact no hx
 have source := clade_clean sub nd inside outside
 have target := clean_agrees shape (fun _ h=>(List.mem_filter.1 h).1)
  (fun _ h=>(List.mem_filter.1 h).1) source
 exact clean_hulls_disjoint T target

theorem target_split_embeddings {T S U : Tree} {p : Vertex} {F : List (List Nat)}
 (sub : CoreGraph.subtree S p=some U) (nd : (leaves S).Nodup)
 (old : pairwiseEmbeddings T F=true) (shapes : F.all (restrictionAgrees T S)=true) :
 pairwiseEmbeddings T (splitForest (leaves U) F)=true := by
 apply split_pairwise_from_local T _ F old
 intro B hb
 exact split_block_pairwise T _ B
  (target_clade_split_disjoint sub nd B (List.all_eq_true.1 shapes B hb))

theorem original_clade_split_agreement : OriginalCladeSplitAgreement := by
 intro T S U p F proper sub hF
 obtain ⟨nt,ns,_⟩ := IndependentReconstruction.proper_parts proper
 have old := hF
 simp only [agreement,Bool.and_eq_true] at old ⊢
 exact ⟨⟨⟨⟨split_partition _ _ F nt old.1.1.1.1,
  split_partition _ _ F ns old.1.1.1.2⟩,split_shapes hF _⟩,
  target_split_embeddings sub ns old.1.2 old.1.1.2⟩,
  source_split_embeddings sub ns old.2⟩

theorem original_clade_split_full {T S U : Tree} {p : Vertex} {F : List (List Nat)}
 (proper : DepthOne.proper T S=true) (sub : CoreGraph.subtree S p=some U)
 (hF : agreement T S F=true) :
 agreement T S (splitForest (leaves U) F)=true ∧
 (splitForest (leaves U) F).length≤F.length+1 ∧
 VertexGeometry.Refines (splitForest (leaves U) F)
  [leaves U,(leaves S).filter (fun x=>!(leaves U).contains x)] := by
 have others := original_split_label_count proper sub hF
 exact ⟨original_clade_split_agreement T S U p F proper sub hF,others.2.2.2,others.2.2.1⟩
end ContactedClade

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedClade.clean_hulls_disjoint
#print axioms ContactedClade.clean_hulls_disjoint
#check @ContactedClade.target_clade_split_disjoint
#print axioms ContactedClade.target_clade_split_disjoint
#check @ContactedClade.target_split_embeddings
#print axioms ContactedClade.target_split_embeddings
#check @ContactedClade.original_clade_split_agreement
#print axioms ContactedClade.original_clade_split_agreement
#check @ContactedClade.original_clade_split_full
#print axioms ContactedClade.original_clade_split_full
