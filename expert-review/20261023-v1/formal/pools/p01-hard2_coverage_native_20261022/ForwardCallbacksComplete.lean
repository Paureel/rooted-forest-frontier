-- Contacted composition of completed generic and original emitted branch interface.
-- Generic proof is reused from a664's exact source rebase; no duplicate forest proof.
import ForwardJoinControls
open RMAF ForestState GenericForest Universal233 OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace ContactedForwardCallbacks

theorem exact_forward_child (actual : Tree→Tree→Nat→Option (List (List Nat)))
 (b : Rule4.Branch) (r : Nat) (ih : ForestMinCompletion.LocalOrdinaryIH r actual) :
 Rule4.ExactChild (rule4Child actual) b r := by
 have sound (G : List (List Nat)) (returned : rule4Child actual b r=some G) :
   Rule4.ChildFeasible b r G := GenericForest.solve_sound actual (some b.target) b.sourceForest r G returned
 have complete (H : List (List Nat)) (feasible : Rule4.ChildFeasible b r H) :
   ∃G,rule4Child actual b r=some G ∧ G.length≤H.length :=
   PaidInstanceForest.forest_completion_obligation r actual ih (some b.target) b.sourceForest H feasible.1 feasible.2
 constructor
 · intro G returned
   refine ⟨sound G returned,?_⟩
   intro H feasible
   obtain ⟨J,answer,least⟩:=complete H feasible
   have eq : J=G := Option.some.inj (answer.symm.trans returned)
   exact eq ▸ least
 · exact complete

theorem affordable_forward_callbacks (ordinary : PaidInstances.OrdinarySolver) (q : Nat)
 {T S : Tree} (s : Rule4.Choice T S) (below : PaidInstances.BelowBudget ordinary q) :
 ContactedForward.ForwardCallbacks (PaidInstances.OwnPaid ordinary q) s q := by
 intro b member affordable
 have strict := (ContactedForward.actual_callback_budget s member affordable).1
 have ih := PaidInstances.local_ordinary_ih ordinary q (q-b.cost) below strict
 exact exact_forward_child (PaidInstances.OwnPaid ordinary q) b (q-b.cost) ih

-- Every original proper/rejected/forward selection guard remains in the printed boundary.
theorem forward_callbacks_printed : ∀ordinary q T S (s : Rule4.Choice T S),
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.rule4Forward s →
 PaidInstances.BelowBudget ordinary q →
 ContactedForward.ForwardCallbacks (PaidInstances.OwnPaid ordinary q) s q := by
 intro ordinary q T S s _ _ _ below
 exact affordable_forward_callbacks ordinary q s below

def ForwardRule4For (ordinary : PaidInstances.OrdinarySolver) : Prop :=
 ∀q T S (s : Rule4.Choice T S),
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.rule4Forward s →
 PaidInstances.BelowBudget ordinary q → QueryExact T S q (runRule4 (PaidInstances.OwnPaid ordinary q) s q)

theorem forward_rule (ordinary : PaidInstances.OrdinarySolver) : ForwardRule4For ordinary := by
 intro q T S s proper rejected selected below
 exact ContactedForward.checked_forward_caller (PaidInstances.OwnPaid ordinary q) q s proper rejected selected
   (affordable_forward_callbacks ordinary q s below)

theorem forward_printed : ∀ordinary q T S (s : Rule4.Choice T S),
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.rule4Forward s →
 PaidInstances.BelowBudget ordinary q → QueryExact T S q (runRule4 (PaidInstances.OwnPaid ordinary q) s q) := forward_rule

theorem forward_some_printed (ordinary : PaidInstances.OrdinarySolver) (q : Nat) {T S : Tree}
 (s : Rule4.Choice T S) (proper : DepthOne.proper T S=true) (rejected : DepthOne.pretest01 T S=.rejected)
 (selected : early T S=.rule4Forward s) (below : PaidInstances.BelowBudget ordinary q)
 (G : List (List Nat)) (returned : runRule4 (PaidInstances.OwnPaid ordinary q) s q=some G) :
 agreement T S G=true ∧ G.length-1≤q ∧ ∀F,agreement T S F=true→G.length≤F.length := by
 have exactQuery:=forward_printed ordinary q T S s proper rejected selected below
 rw [returned] at exactQuery
 exact exactQuery

theorem forward_none_printed (ordinary : PaidInstances.OrdinarySolver) (q : Nat) {T S : Tree}
 (s : Rule4.Choice T S) (proper : DepthOne.proper T S=true) (rejected : DepthOne.pretest01 T S=.rejected)
 (selected : early T S=.rule4Forward s) (below : PaidInstances.BelowBudget ordinary q)
 (returned : runRule4 (PaidInstances.OwnPaid ordinary q) s q=none) :
 ∀F,agreement T S F=true→q<F.length-1 := by
 have exactQuery:=forward_printed ordinary q T S s proper rejected selected below
 rw [returned] at exactQuery
 exact exactQuery

#print forward_callbacks_printed
#print forward_printed
#print forward_some_printed
#print forward_none_printed
#print axioms forward_callbacks_printed
#print axioms forward_printed
end ContactedForwardCallbacks

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForwardCallbacks.exact_forward_child
#print axioms ContactedForwardCallbacks.exact_forward_child
#check @ContactedForwardCallbacks.affordable_forward_callbacks
#print axioms ContactedForwardCallbacks.affordable_forward_callbacks
#check @ContactedForwardCallbacks.forward_callbacks_printed
#print axioms ContactedForwardCallbacks.forward_callbacks_printed
#check @ContactedForwardCallbacks.forward_rule
#print axioms ContactedForwardCallbacks.forward_rule
#check @ContactedForwardCallbacks.forward_printed
#print axioms ContactedForwardCallbacks.forward_printed
#check @ContactedForwardCallbacks.forward_some_printed
#print axioms ContactedForwardCallbacks.forward_some_printed
#check @ContactedForwardCallbacks.forward_none_printed
#print axioms ContactedForwardCallbacks.forward_none_printed
