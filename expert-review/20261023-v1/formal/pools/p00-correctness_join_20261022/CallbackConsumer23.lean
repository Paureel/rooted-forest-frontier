-- Actual callback and minimum consumer with every missing bridge named explicitly.
import StrictBudget04
import ForestSound21
import PaidChildren
open RMAF OrdinaryDispatch Universal233 Universal233.CherryBranching
namespace HighCompletion
def ForestLocalCompleteAt (r : Nat) (actual : Tree→Tree→Nat→Option (List (List Nat))) : Prop :=
 ∀ T ss G,ForestState.agrees T ss G=true → ForestState.additionalCost ss G≤r →
   ∃F,GenericForest.solve actual T ss r=some F ∧ F.length≤G.length
-- This is precisely the still-unproved completeness/minimum half of the refused lower grant.
def ForestCompletionObligation : Prop := ∀r actual,
 ForestMinCompletion.LocalOrdinaryIH r actual → ForestLocalCompleteAt r actual
structure ChildStateBridge (T S : Tree) (c : Child) : Prop where
 sound : ∀F,ForestState.agrees (some T) c.sourceForest F=true → agreement T S F=true
 budget : ∀q F,c.paid≤q → ForestState.agrees (some T) c.sourceForest F=true →
   ForestState.additionalCost c.sourceForest F≤q-c.paid → F.length-1≤q
 transfer : ∀q G,agreement T S G=true → VertexGeometry.Refines G c.partition → G.length-1≤q →
   c.paid≤q ∧ ForestState.agrees (some T) c.sourceForest G=true ∧
     ForestState.additionalCost c.sourceForest G≤q-c.paid
theorem actual_child_success (actual : Tree→Tree→Nat→Option (List (List Nat)))
    (T S : Tree) (q : Nat) (c : Child) (bridge : ChildStateBridge T S c)
    (F : List (List Nat)) (hcall : childCall (forestChild actual T) q c=some F) :
    ordinaryAccepted T S q F=true := by
  unfold childCall remaining at hcall
  split at hcall
  next hpaid =>
    have hsolve : GenericForest.solve actual (some T) c.sourceForest (q-c.paid)=some F := hcall
    have hf:=forest_solve_sound actual (some T) c.sourceForest (q-c.paid) F hsolve
    simp only [ordinaryAccepted,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨bridge.sound F hf.1,bridge.budget q F hpaid hf.1 hf.2⟩
  next => cases hcall
theorem actual_child_complete (ordinary : OrdinarySolver) (q : Nat)
    (below : BelowBudget ordinary q) (forestComplete : ForestCompletionObligation)
    (T S : Tree) (c : Child) (hpos : 0<c.paid) (bridge : ChildStateBridge T S c)
    (G : List (List Nat)) (hag : agreement T S G=true) (href : VertexGeometry.Refines G c.partition)
    (hcost : G.length-1≤q) :
    ∃F,childCall (forestChild (OwnPaid ordinary q) T) q c=some F ∧
      ordinaryAccepted T S q F=true ∧ F.length≤G.length := by
  have ht:=bridge.transfer q G hag href hcost
  have hr : q-c.paid<q := by omega
  have hIH:=local_ordinary_ih ordinary q (q-c.paid) below hr
  obtain ⟨F,hF,hlen⟩:=forestComplete (q-c.paid) (OwnPaid ordinary q) hIH (some T) c.sourceForest G ht.2.1 ht.2.2
  have hcall : childCall (forestChild (OwnPaid ordinary q) T) q c=some F := by
    simpa only [childCall,remaining,if_pos ht.1,Option.bind_some,forestChild] using hF
  exact ⟨F,hcall,actual_child_success (OwnPaid ordinary q) T S q c bridge F hcall,hlen⟩
theorem answers_complete_of_children (ordinary : OrdinarySolver) (q : Nat)
    (below : BelowBudget ordinary q) (forestComplete : ForestCompletionObligation)
    (T S : Tree) (children : List Child)
    (hpos : ∀c∈children,0<c.paid) (bridge : ∀c∈children,ChildStateBridge T S c)
    (geometry : ∀G,agreement T S G=true → ∃c∈children,VertexGeometry.Refines G c.partition) :
    AnswersComplete T S q (childAnswers (OwnPaid ordinary q) T q children) := by
  intro G hag hcost
  obtain ⟨c,hc,href⟩:=geometry G hag
  obtain ⟨F,hcall,haccept,hlen⟩:=actual_child_complete ordinary q below forestComplete T S c (hpos c hc) (bridge c hc) G hag href hcost
  exact ⟨F,List.mem_filterMap.mpr ⟨c,hc,hcall⟩,haccept,hlen⟩
theorem run_children_query_exact (ordinary : OrdinarySolver) (q : Nat)
    (below : BelowBudget ordinary q) (forestComplete : ForestCompletionObligation)
    (T S : Tree) (children : List Child)
    (hpos : ∀c∈children,0<c.paid) (bridge : ∀c∈children,ChildStateBridge T S c)
    (geometry : ∀G,agreement T S G=true → ∃c∈children,VertexGeometry.Refines G c.partition) :
    QueryExact T S q (runChildren (OwnPaid ordinary q) T S q children) := by
  exact query_exact_of_answers_complete T S q _
    (answers_complete_of_children ordinary q below forestComplete T S children hpos bridge geometry)
#print axioms actual_child_success
#print axioms run_children_query_exact
end HighCompletion
