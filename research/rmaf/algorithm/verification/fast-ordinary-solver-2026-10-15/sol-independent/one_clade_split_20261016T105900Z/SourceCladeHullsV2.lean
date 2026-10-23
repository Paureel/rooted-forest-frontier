/- Contacted prover: source clade pieces have disjoint original hulls. -/
import HullSubset
open RMAF ForestState Universal233 Universal233.HardParent
open IndependentGeometry IndependentOneExchange
namespace ContactedClade

theorem span_child (D : List Nat) (l r : Tree) (side : Bool) (v : Vertex)
 (h : side::v∈rootedSpan D (.node l r)) :
 v∈rootedSpan D (if side then r else l) := by
 simp only [rootedSpan] at h
 split at h
 · simp at h
 · cases side <;> simpa [prependSide] using h

theorem clade_span_disjoint {S U : Tree} {p : Vertex} {A D : List Nat}
 (sub : CoreGraph.subtree S p=some U) (nd : (leaves S).Nodup)
 (inside : ∀x∈A,x∈leaves U) (outside : ∀x∈leaves U,x∉D) :
 ∀v∈minimalVertices A S,v∉rootedSpan D S := by
 induction p generalizing S with
 | nil =>
  have eq : S=U := by simpa [CoreGraph.subtree] using sub
  subst S
  have zero := span_absent U D outside
  simp [zero]
 | cons side rest ih =>
  cases S with
  | leaf y => simp [CoreGraph.subtree] at sub
  | node l r =>
   have ns := List.nodup_append.1 nd
   cases side
   · change CoreGraph.subtree l rest=some U at sub
     have zero : rootedSpan A r=[] := by
      apply span_absent
      intro x xr xa
      have xl := subtree_leaves_own sub x (inside x xa)
      exact ns.2.2 x xl x xr rfl
     have er : (rootedSpan A r).isEmpty=true := by simp [zero]
     rw [minimal_node_left A l r er]
     intro v hv member
     obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
     exact ih sub ns.1 w hw (span_child D l r false w member)
   · change CoreGraph.subtree r rest=some U at sub
     have zero : rootedSpan A l=[] := by
      apply span_absent
      intro x xl xa
      have xr := subtree_leaves_own sub x (inside x xa)
      exact ns.2.2 x xl x xr rfl
     have el : (rootedSpan A l).isEmpty=true := by simp [zero]
     rw [minimal_node_right A l r el]
     intro v hv member
     obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
     exact ih sub ns.2.1 w hw (span_child D l r true w member)

theorem clade_split_disjoint {S U : Tree} {p : Vertex}
 (sub : CoreGraph.subtree S p=some U) (nd : (leaves S).Nodup) (B : List Nat) :
 disjointVertices (minimalVertices (B.filter (leaves U).contains) S)
  (minimalVertices (B.filter (fun x=>!(leaves U).contains x)) S)=true := by
 have inside : ∀x∈B.filter (leaves U).contains,x∈leaves U := by
  intro x hx;exact List.contains_iff_mem.1 (List.mem_filter.1 hx).2
 have outside : ∀x∈leaves U,x∉B.filter (fun x=>!(leaves U).contains x) := by
  intro x hx hd
  have no : x∉leaves U := by simpa using (List.mem_filter.1 hd).2
  exact no hx
 apply List.all_eq_true.2
 intro v hv
 have no : v∉minimalVertices (B.filter (fun x=>!(leaves U).contains x)) S := by
  intro member
  exact clade_span_disjoint sub nd inside outside v hv
   (minimal_in_span _ _ v member)
 simpa using no

theorem split_piece_subset (X B A : List Nat) (h : A∈splitBlock X B) : ∀x∈A,x∈B := by
 have choices := (List.mem_filter.1 h).1
 simp only [List.mem_cons,List.not_mem_nil,or_false] at choices
 rcases choices with rfl|rfl <;> exact fun x hx=>(List.mem_filter.1 hx).1

theorem pairwise_append_own (T : Tree) (L R : List (List Nat))
 (hl : pairwiseEmbeddings T L=true) (hr : pairwiseEmbeddings T R=true)
 (cross : ∀A∈L,∀B∈R,disjointVertices (minimalVertices A T) (minimalVertices B T)=true) :
 pairwiseEmbeddings T (L++R)=true := by
 induction L with
 | nil => exact hr
 | cons A tail ih =>
  simp only [List.cons_append,pairwiseEmbeddings,Bool.and_eq_true] at hl ⊢
  constructor
  · apply List.all_eq_true.2
    intro B hB
    rcases List.mem_append.1 hB with ht|ht
    · exact List.all_eq_true.1 hl.1 B ht
    · exact cross A (by simp) B ht
  · exact ih hl.2 (fun B hb=>cross B (by simp [hb]))

theorem split_pairwise_from_local (T : Tree) (X : List Nat) (F : List (List Nat))
 (old : pairwiseEmbeddings T F=true)
 (pieces : ∀B∈F,pairwiseEmbeddings T (splitBlock X B)=true) :
 pairwiseEmbeddings T (splitForest X F)=true := by
 induction F with
 | nil => rfl
 | cons B rest ih =>
  simp only [pairwiseEmbeddings,Bool.and_eq_true] at old
  change pairwiseEmbeddings T (splitBlock X B++splitForest X rest)=true
  apply pairwise_append_own T _ _ (pieces B (by simp))
   (ih old.2 (fun D hD=>pieces D (by simp [hD])))
  intro A ha C hc
  obtain ⟨D,hD,hc⟩ := List.mem_flatMap.1 hc
  exact disjoint_subsets T (split_piece_subset X B A ha) (split_piece_subset X D C hc)
   (List.all_eq_true.1 old.1 D hD)

theorem split_block_pairwise (T : Tree) (X B : List Nat)
 (cross : disjointVertices (minimalVertices (B.filter X.contains) T)
  (minimalVertices (B.filter (fun x=>!X.contains x)) T)=true) :
 pairwiseEmbeddings T (splitBlock X B)=true := by
 apply pairwise_filter
 simpa [pairwiseEmbeddings] using cross

theorem source_split_embeddings {S U : Tree} {p : Vertex} {F : List (List Nat)}
 (sub : CoreGraph.subtree S p=some U) (nd : (leaves S).Nodup)
 (old : pairwiseEmbeddings S F=true) :
 pairwiseEmbeddings S (splitForest (leaves U) F)=true := by
 apply split_pairwise_from_local S _ F old
 intro B _
 exact split_block_pairwise S _ B (clade_split_disjoint sub nd B)
end ContactedClade
