/- Authored reverse Rule4 bridge. Completed source/geometry and generic completeness
are reused with permanent contact/compiler/native/helper qualifications. No independent credit. -/
import ForwardCallerR3
import SelectedInstance10
open RMAF ForestState Universal233 OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace AuthoredReverse

/-- Literal original reverse Choice branch order. The callback is never swapped. -/
theorem reverse_literal_order {T S : Tree} (s : Rule4.Choice S T) :
 (Rule4.branches s).map Rule4.Branch.target=[S,S,T] ∧
 (Rule4.branches s).map Rule4.Branch.source=[T,T,S] ∧
 (Rule4.branches s).map Rule4.Branch.swapped=[false,false,true] := ⟨rfl,rfl,rfl⟩

/-- Convert QueryExact by agreement symmetry, including every competing forest.
No statement about early S T or symmetry of any callback occurs. -/
theorem query_original_orientation {T S : Tree} {q : Nat} {answer : Option CommonForest}
 (h : QueryExact S T q answer) : QueryExact T S q answer := by
 cases answer with
 | none => intro F hF;exact h F (IndependentGeometry.agreement_swap hF)
 | some F =>
   refine ⟨IndependentGeometry.agreement_swap h.1,h.2.1,?_⟩
   intro G hG
   exact h.2.2 G (IndependentGeometry.agreement_swap hG)

/-- Generic completeness is invoked once on the unchanged literal ForestState.
This is a small Rule4.ExactChild interface bridge, not a second generic proof. -/
theorem exact_rule4_child (actual : Tree→Tree→Nat→Option GenericForest.Forest)
 (b : Rule4.Branch) (r : Nat) (ih : ForestMinCompletion.LocalOrdinaryIH r actual) :
 Rule4.ExactChild (rule4Child actual) b r := by
 have sound (G : GenericForest.Forest) (ret : rule4Child actual b r=some G) :
   Rule4.ChildFeasible b r G := GenericForest.solve_sound actual (some b.target) b.sourceForest r G ret
 have complete (H : GenericForest.Forest) (hH : Rule4.ChildFeasible b r H) :
   ∃G,rule4Child actual b r=some G ∧ G.length≤H.length := by
   exact PaidInstanceForest.forest_completion_obligation r actual ih (some b.target) b.sourceForest H hH.1 hH.2
 refine ⟨?_,complete⟩
 intro G ret
 have hs:=sound G ret
 refine ⟨hs,?_⟩
 intro H hH
 obtain ⟨F,hF,least⟩:=complete H hH
 have eq : F=G := Option.some.inj (hF.symm.trans ret)
 simpa only [eq] using least

/-- Exact actual affine calls, indexed by the original reversed Choice. -/
def ReverseCallbacks (actual : Tree→Tree→Nat→Option CommonForest)
 {T S : Tree} (s : Rule4.Choice S T) (q : Nat) : Prop :=
 ∀b∈Rule4.branches s,b.cost≤q→Rule4.ExactChild (rule4Child actual) b (q-b.cost)

theorem reverse_callbacks (ordinary : PaidInstances.OrdinarySolver) (q : Nat)
 {T S : Tree} (s : Rule4.Choice S T) (below : PaidInstances.BelowBudget ordinary q) :
 ReverseCallbacks (PaidInstances.OwnPaid ordinary q) s q := by
 intro b member affordable
 have strict:=(ContactedForward.actual_callback_budget s member affordable).1
 exact exact_rule4_child (PaidInstances.OwnPaid ordinary q) b (q-b.cost)
   (PaidInstances.local_ordinary_ih ordinary q (q-b.cost) below strict)

/-- Source/materialization/bill/positive fee and strict residual budget for every
actual affordable child, retaining completed geometry as explicit named origins. -/
theorem reverse_source_payment {T S : Tree} (s : Rule4.Choice S T)
 {b : Rule4.Branch} (member : b∈Rule4.branches s) {q : Nat} (affordable : b.cost≤q) :
 b.sourceForest.length=b.partition.length ∧
 ForestState.proper (some b.target) b.sourceForest=true ∧
 (∀F,ForestState.agrees (some b.target) b.sourceForest F=true ↔ ContactedForward.OriginalCovered S T b F) ∧
 1≤b.cost ∧ b.cost+1=b.partition.length ∧ q-b.cost<q ∧ b.cost+(q-b.cost)=q := by
 have material:=ContactedForward.emitted_materialized_scope s member
 have literal:=ContactedForward.emitted_literal_checks s b member
 have paid:=ContactedForward.emitted_paid_positive s b member
 have budget:=ContactedForward.actual_callback_budget s member affordable
 exact ⟨material.1,material.2.1,material.2.2,paid,literal.2.2.1,budget.1,budget.2⟩

theorem reverse_query_from_callbacks (actual : Tree→Tree→Nat→Option CommonForest) (q : Nat)
 {T S : Tree} (s : Rule4.Choice S T) (callback : ReverseCallbacks actual s q) :
 QueryExact T S q (runRule4 actual s q) := by
 apply query_original_orientation
 cases returned : runRule4 actual s q with
 | none =>
   intro F hF
   by_cases budget : F.length-1≤q
   · obtain ⟨G,hG,_⟩:=ContactedForward.forward_caller_complete s actual q callback F hF budget
     rw [returned] at hG;cases hG
   · omega
 | some G =>
   have sound:=ContactedForward.forward_caller_sound s actual q callback returned
   refine ⟨sound.1,sound.2,?_⟩
   intro F hF
   by_cases budget : F.length-1≤q
   · obtain ⟨B,hB,least⟩:=ContactedForward.forward_caller_complete s actual q callback F hF budget
     have eq : B=G := Option.some.inj (hB.symm.trans returned)
     exact eq ▸ least
   · omega

/-- Original guard and actual callback argument order retained verbatim. -/
def ReverseRuleFor (ordinary : PaidInstances.OrdinarySolver) : Prop := ∀q T S (s : Rule4.Choice S T),
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.rule4Reverse s →
 PaidInstances.BelowBudget ordinary q → QueryExact T S q (runRule4 (PaidInstances.OwnPaid ordinary q) s q)

theorem reverse_rule (ordinary : PaidInstances.OrdinarySolver) : ReverseRuleFor ordinary := by
 intro q T S s _proper _rejected _selected below
 exact reverse_query_from_callbacks (PaidInstances.OwnPaid ordinary q) q s (reverse_callbacks ordinary q s below)

end AuthoredReverse
