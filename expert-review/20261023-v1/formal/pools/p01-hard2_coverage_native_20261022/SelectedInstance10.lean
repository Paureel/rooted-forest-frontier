-- Actual selected-one current callbacks, using the source-rebased generic proof.
-- CONTACTED/source-guided reuse; no independent/blind/reconstruction credit.
import StrictControl07
open RMAF ForestState OrdinaryDispatch Universal233 Universal233.CherryBranching
namespace PaidInstances

theorem local_ordinary_ih (ordinary : OrdinarySolver) (q r : Nat)
 (below : BelowBudget ordinary q) (strict : r<q) :
 ForestMinCompletion.LocalOrdinaryIH r (OwnPaid ordinary q) := by
 constructor
 · intro t s b F hb proper answer
   have bq : b<q := Nat.lt_of_le_of_lt hb strict
   have actual : ordinary b t s=some F := by simpa only [OwnPaid,if_pos bq] using answer
   have ex:=below b bq t s proper
   rw [actual] at ex
   exact ex
 · intro t s b G hb proper agree budget
   have bq : b<q := Nat.lt_of_le_of_lt hb strict
   have ex:=below b bq t s proper
   cases actual : ordinary b t s with
   | none =>
     rw [actual] at ex
     exact False.elim (Nat.not_lt_of_ge budget (ex G agree))
   | some F => exact ⟨F,by simp only [OwnPaid,if_pos bq,actual]⟩

theorem exact_child_of_materialized (actual : Tree→Tree→Nat→Option Forest)
 (T S : Tree) (child : Child) (r : Nat)
 (ih : ForestMinCompletion.LocalOrdinaryIH r actual)
 (len : child.sourceForest.length=child.partition.length)
 (equiv : ∀F,ForestState.agrees (some T) child.sourceForest F=true ↔ feasible T S child F) :
 ExactChildAt T S (forestChild actual T) child r := by
 have sound (G : Forest) (h : forestChild actual T child r=some G) :
   feasible T S child G ∧ G.length-child.partition.length≤r := by
   have hs:=GenericForest.solve_sound actual (some T) child.sourceForest r G h
   exact ⟨(equiv G).mp hs.1,by simpa only [additionalCost,len] using hs.2⟩
 have complete (H : Forest) (hH : feasible T S child H)
   (budget : H.length-child.partition.length≤r) :
   ∃G,forestChild actual T child r=some G ∧ G.length≤H.length := by
   exact PaidInstanceForest.forest_completion_obligation r actual ih (some T) child.sourceForest H
     ((equiv H).mpr hH) (by simpa only [additionalCost,len] using budget)
 refine ⟨?_,?_⟩
 · constructor
   · rintro ⟨G,hG⟩
     exact ⟨G,(sound G hG).1,(sound G hG).2⟩
   · rintro ⟨H,hH,budget⟩
     obtain ⟨G,hG,_⟩:=complete H hH budget
     exact ⟨G,hG⟩
 · intro G hG
   have hs:=sound G hG
   refine ⟨⟨hs.1,?_⟩,hs.2⟩
   intro H hH
   by_cases budget : H.length-child.partition.length≤r
   · obtain ⟨F,hF,least⟩:=complete H hH budget
     have eq : F=G := Option.some.inj (hF.symm.trans hG)
     simpa only [eq] using least
   · have bound:=hs.2
     omega

theorem selected_current_children (ordinary : OrdinarySolver) (q : Nat)
 {T S : Tree} {reverse : Bool} {c : Candidate}
 (proper : DepthOne.proper T S=true) (selected : FastOrdinary.early T S=.one reverse c)
 (below : BelowBudget ordinary q) :
 IndependentPaid.CurrentChildren (OwnPaid ordinary q)
  (FastOrdinary.Oriented reverse T S).1 (FastOrdinary.Oriented reverse T S).2 q
  [pendantChild (FastOrdinary.Oriented reverse T S).2 c.a c.b] := by
 intro child hc r rem
 have eq : child=pendantChild (FastOrdinary.Oriented reverse T S).2 c.a c.b := by simpa only [List.mem_singleton] using hc
 subst child
 have ready:=ContactedOneConsumer.selected_literal_and_coverage proper selected
 have strict:=IndependentPaid.remaining_strict ready.2.2.2.2.1 rem
 have ih:=local_ordinary_ih ordinary q r below strict
 have material:=ContactedOneConsumer.selected_materialized_scope proper selected
 exact exact_child_of_materialized (OwnPaid ordinary q) _ _ _ r ih material.1 material.2.2.1

def OneRuleFor (ordinary : OrdinarySolver) : Prop := ∀q T S reverse c,
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → FastOrdinary.early T S=.one reverse c →
 BelowBudget ordinary q → QueryExact T S q (runChildren (OwnPaid ordinary q)
  (FastOrdinary.Oriented reverse T S).1 (FastOrdinary.Oriented reverse T S).2 q
  [pendantChild (FastOrdinary.Oriented reverse T S).2 c.a c.b])

theorem one_rule (ordinary : OrdinarySolver) : OneRuleFor ordinary := by
 intro q T S reverse c proper rejected selected below
 exact ContactedOneConsumer.checked_one_caller (OwnPaid ordinary q) q proper rejected selected
   (selected_current_children ordinary q proper selected below)
#print axioms selected_current_children
#print axioms one_rule
end PaidInstances

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @PaidInstances.local_ordinary_ih
#print axioms PaidInstances.local_ordinary_ih
#check @PaidInstances.exact_child_of_materialized
#print axioms PaidInstances.exact_child_of_materialized
#check @PaidInstances.selected_current_children
#print axioms PaidInstances.selected_current_children
#check @PaidInstances.one_rule
#print axioms PaidInstances.one_rule
