-- Exact remaining source boundary obligation, with its universal consumer.
-- SourceBoundaryObligation is an assumption here, never asserted as proved.
import Restriction25
open RMAF Universal233
namespace OwnHigh
def NoPendantCrossing (S : Tree) (a b : Nat) (F : List (List Nat)) : Prop :=
  ∀ v ∈ CherryBranching.cuts S a b, ∀ P ∈ F, ∀ x ∈ P,
    x ∈ HardParent.subtreeLabels S v → ∀ y ∈ P, y ∈ HardParent.subtreeLabels S v
theorem refines_of_no_crossing (S : Tree) (a b : Nat) (F : List (List Nat))
    (hpart : partitionCheck (leaves S) F = true) (hc : NoPendantCrossing S a b F) :
    VertexGeometry.Refines F (CherryBranching.pendantPartition S a b) := by
  intro P hp
  by_cases hhit : ∃ v ∈ CherryBranching.cuts S a b, ∃ x ∈ P, x ∈ HardParent.subtreeLabels S v
  · obtain ⟨v,hv,x,hx,hxv⟩ := hhit
    refine ⟨HardParent.subtreeLabels S v, ?_, hc v hv P hp x hx hxv⟩
    exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨v,hv,rfl⟩))
  · refine ⟨CherryBranching.coreLabels S a b, ?_, ?_⟩
    · exact List.mem_append.mpr (.inr (by simp))
    · intro x hx
      have hl := block_subset (leaves S) F hpart P hp x hx
      simp only [CherryBranching.coreLabels, List.mem_filter, Bool.not_eq_true']
      refine ⟨hl, Bool.eq_false_iff.mpr ?_⟩
      intro hcontains
      obtain ⟨R,hr,hxr⟩ := List.mem_flatten.mp (List.contains_iff_mem.mp hcontains)
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
      exact hhit ⟨v,hv,x,hx,hxr⟩
def SourceBoundaryObligation : Prop :=
  ∀ (S : Tree) (a b : Nat) (F : List (List Nat)) (P : List Nat),
    (leaves S).Nodup → a ≠ b → partitionCheck (leaves S) F = true →
    pairwiseEmbeddings S F = true → P ∈ F → a ∈ P → b ∈ P →
    (∃ U, restrict P S = some U ∧ HasCherry U a b) → NoPendantCrossing S a b F
theorem literal_consumer (hboundary : SourceBoundaryObligation)
    (T S : Tree) (p : Vertex) (a b : Nat) (F : List (List Nat))
    (hproper : DepthOne.proper T S = true) (hc : CoreGraph.CherryAt T p a b)
    (hag : agreement T S F = true) :
    [a] ∈ F ∨ [b] ∈ F ∨ VertexGeometry.Refines F (CherryBranching.pendantPartition S a b) := by
  rcases agreement_singleton_or_shared T S p a b F hc hag with has | hbs | ⟨P,hp,ha,hb⟩
  · exact Or.inl has
  · exact Or.inr (Or.inl hbs)
  · have hres := agreement_source_cherry T S p a b F P hc hag hp ha hb
    have hab := cherry_distinct T S p a b hproper hc
    have hs : (leaves S).Nodup := by
      simp only [DepthOne.proper, Bool.and_eq_true, decide_eq_true_eq] at hproper
      exact hproper.1.2
    have hag' := hag
    simp only [agreement, Bool.and_eq_true] at hag'
    have hpart : partitionCheck (leaves S) F = true := hag'.1.1.1.2
    have hemb : pairwiseEmbeddings S F = true := hag'.2
    have hn := hboundary S a b F P hs hab hpart hemb hp ha hb hres
    exact Or.inr (Or.inr (refines_of_no_crossing S a b F hpart hn))
#print axioms refines_of_no_crossing
#print axioms literal_consumer
#print SourceBoundaryObligation
#check literal_consumer
end OwnHigh
