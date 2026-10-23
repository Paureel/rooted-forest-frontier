import DisjointOriginalArms40
open RMAF Universal233 CherryBranching OrdinaryDispatch RestrictionBridge
namespace FreshLiteralDisjoint
/-- A logical consumer of the saved parent-refining query contract. This does not
supply the still-needed cohabitation-to-refinement implication. -/
theorem refining_answer_valid (T S : Tree) (P : List (List Nat)) (q : Nat)
 (out : Option (List (List Nat))) (spec : RefiningQueryExact T S P q out) :
 ∀G,out=some G → agreement T S G=true ∧ G.length-1≤q := by
 cases out with
 | none => intro G h;cases h
 | some F =>
  intro G h
  cases h
  exact ⟨spec.1,spec.2.2.1⟩

theorem refining_competitor_cover (T S : Tree) (P : List (List Nat)) (q : Nat)
 (out : Option (List (List Nat))) (spec : RefiningQueryExact T S P q out) :
 ∀F,agreement T S F=true → Refines F P → F.length-1≤q →
   ∃G,out=some G ∧ G.length≤F.length := by
 cases out with
 | none =>
  intro F hag href afford
  have low:=spec F hag href
  omega
 | some G =>
  intro F hag href afford
  exact ⟨G,rfl,spec.2.2.2 F hag href⟩

theorem original_parent_valid_cover_and_strict (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (selected : FastOrdinary.early T S=.hard2 c d)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (below : IndependentReconstruction.BelowBudget q) :
 let paid:=DisjointParents.query (IndependentReconstruction.OwnPaid q) T S (pendantPartition S c.a c.b) q
 (∀G,paid.answer=some G → agreement T S G=true ∧ G.length-1≤q) ∧
 (∀F,agreement T S F=true → Refines F (pendantPartition S c.a c.b) → F.length-1≤q →
   ∃G,paid.answer=some G ∧ G.length≤F.length) ∧
 ∀call∈paid.calls,call.budget<q := by
 dsimp only
 obtain ⟨spec,strict⟩:=original_parent_query_and_strict q T S c d proper selected picked below
 exact ⟨refining_answer_valid T S _ q _ spec,refining_competitor_cover T S _ q _ spec,strict⟩
end FreshLiteralDisjoint
#print axioms FreshLiteralDisjoint.refining_answer_valid
#print axioms FreshLiteralDisjoint.refining_competitor_cover
#print axioms FreshLiteralDisjoint.original_parent_valid_cover_and_strict

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshLiteralDisjoint.refining_answer_valid
#print axioms FreshLiteralDisjoint.refining_answer_valid
#check @FreshLiteralDisjoint.refining_competitor_cover
#print axioms FreshLiteralDisjoint.refining_competitor_cover
#check @FreshLiteralDisjoint.original_parent_valid_cover_and_strict
#print axioms FreshLiteralDisjoint.original_parent_valid_cover_and_strict
