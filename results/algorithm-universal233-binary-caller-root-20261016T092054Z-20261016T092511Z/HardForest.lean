import HardPaid

namespace Universal233.PairAssembly
open RMAF CoreGraph CoreProgram SourceCoverage VertexGeometry CutRealization PaidAssembly

theorem component_of_literal_leafset {S : Tree} (hs : (leaves S).Nodup)
    (cuts : List RMAF.Vertex) (r : RMAF.Vertex) (L : List Nat)
    (hr : Valid S r) (hne : L ≠ [])
    (hex : ∀ x, x ∈ L ↔ ∃ v, LeafAt S v x ∧ ResidualWalk S cuts r v) :
    ComponentLabels S cuts r L := by
  refine ⟨hr,?_,hne,?_⟩
  · intro x hx
    obtain ⟨v,hv,_⟩ := (hex x).1 hx
    exact ⟨v,hv⟩
  · intro a x ha
    constructor
    · intro hx
      obtain ⟨v,hv,hwalk⟩ := (hex x).1 hx
      have he : a = v := leaf_unique hs ha hv
      simpa only [he] using hwalk
    · intro hwalk
      exact (hex x).2 ⟨a,ha,hwalk⟩

/-- Literal original hard2 parent sets are an ACTUAL source forest. This fills
E's source-parent embedding premise from residual components, not an assumption. -/
theorem hard_parent_embeddings {S : Tree} (hs : (leaves S).Nodup)
    {p r : RMAF.Vertex} (h : HardParent.LiteralOriginalThree S p r) :
    pairwiseEmbeddings S [leftParent S p,rightParent S r,rootParent S p r] = true := by
  let cs : List (RMAF.Vertex × List Nat) :=
    [(p,leftParent S p),(r,rightParent S r),([],rootParent S p r)]
  have hc : ∀ v L, (v,L) ∈ cs → ComponentLabels S [p,r] v L := by
    intro v L hm
    simp only [cs,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hm
    rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact component_of_literal_leafset hs _ _ _ h.actual_left h.nonempty_left (fun x => (h.leafsets x).1)
    · exact component_of_literal_leafset hs _ _ _ h.actual_right h.nonempty_right (fun x => (h.leafsets x).2.1)
    · exact component_of_literal_leafset hs _ _ _ (Integration.valid_root S) h.nonempty_root (fun x => (h.leafsets x).2.2)
  have hn : (cs.map Prod.fst).Nodup := by
    simp [cs,h.distinct,h.nonroot_left,h.nonroot_right]
  have hsep : ∀ v, v ∈ cs.map Prod.fst → ∀ w, w ∈ cs.map Prod.fst → ResidualWalk S [p,r] v w → v=w := by
    intro v hv w hw hwalk
    apply h.separated v w _ _ hwalk
    · simpa [cs,or_comm,or_left_comm,or_assoc] using hv
    · simpa [cs,or_comm,or_left_comm,or_assoc] using hw
  exact Assembly.components_pairwise_embeddings S [p,r] cs hc hn hsep
end Universal233.PairAssembly
