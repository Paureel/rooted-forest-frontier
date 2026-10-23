-- Own case analysis of the actual Early selector, never early_sound.
import SelectorFacts11
open RMAF Universal233 CherryBranching OrdinaryDispatch FastOrdinary
namespace HighSelector
theorem early_high_selected (T S : Tree) (reverse : Bool) (c : Candidate)
    (h : early T S=.high reverse c) :
    select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.high,c) := by
  unfold early at h
  split at h <;> (try split at h) <;> (try split at h) <;>
    (try contradiction) <;> (try cases h) <;>
    simp_all only [Oriented,Bool.false_eq_true,ite_false,ite_true]
theorem high_selector_facts (T S : Tree) (reverse : Bool) (c : Candidate)
    (hp : DepthOne.proper T S=true) (he : early T S=.high reverse c) :
    DepthOne.proper (Oriented reverse T S).1 (Oriented reverse T S).2=true ∧
    CoreGraph.CherryAt (Oriented reverse T S).1 c.parent c.a c.b ∧
    c.originalCuts=cuts (Oriented reverse T S).2 c.a c.b ∧
    3≤(cuts (Oriented reverse T S).2 c.a c.b).length := by
  have hs := selected_high _ _ c (early_high_selected T S reverse c he)
  have hc := candidate_fields _ _ c hs.1
  exact ⟨proper_oriented T S reverse hp,hc.1,hc.2,hc.2 ▸ hs.2⟩
theorem actual_high_geometry (T S : Tree) (reverse : Bool) (c : Candidate)
    (hp : DepthOne.proper T S=true) (he : early T S=.high reverse c)
    (F : List (List Nat))
    (hag : agreement (Oriented reverse T S).1 (Oriented reverse T S).2 F=true) :
    ∃ child ∈ branches (Oriented reverse T S).2 c.a c.b, VertexGeometry.Refines F child.partition := by
  have hs := high_selector_facts T S reverse c hp he
  exact SourceBoundary.branches_geometry _ _ c.parent c.a c.b F hs.1 hs.2.1 hag
#print axioms high_selector_facts
#print axioms actual_high_geometry
end HighSelector
