import DisjointQuery
import Optimality01
import ActualExecutionAliasesNative
open RMAF Universal233 RestrictionBridge OrdinaryDispatch
namespace FreshLiteralDisjoint
/-- Budget is the original total cut budget. Comparators must refine the literal parent partition. -/
def RefiningQueryExact (T S : Tree) (P : List (List Nat)) (q : Nat) (o : Option (List (List Nat))) : Prop :=
 match o with
 | none => ∀G,agreement T S G=true → Refines G P → q<G.length-1
 | some F => agreement T S F=true ∧ Refines F P ∧ F.length-1≤q ∧
     ∀G,agreement T S G=true → Refines G P → F.length≤G.length

theorem query_parent_contract (q : Nat) (below : IndependentReconstruction.BelowBudget q)
 (T S : Tree) (P : List (List Nat))
 (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
 (pt : partitionCheck (leaves T) P=true) (ps : partitionCheck (leaves S) P=true)
 (et : pairwiseEmbeddings T P=true) (es : pairwiseEmbeddings S P=true)
 (three : P.length=3) :
 RefiningQueryExact T S P q
   (DisjointParents.query (IndependentReconstruction.OwnPaid q) T S P q).answer ∧
 ∀c∈(DisjointParents.query (IndependentReconstruction.OwnPaid q) T S P q).calls,c.budget<q := by
 unfold DisjointParents.query
 by_cases affordable : P.length-1≤q
 · rw [if_pos affordable]
   obtain ⟨spec,strict⟩:=ActualOrdinaryExecution.literal_parent_contract q below T S P nt ns pt ps et es affordable (by omega)
   refine ⟨?_,strict⟩
   cases out : (BothBad.ordinaryExecution (GenericForest.solve (IndependentReconstruction.OwnPaid q))
       T S P (q-(P.length-1))).answer with
   | none =>
     rw [out] at spec
     change RefiningQueryExact T S P q (BothBad.checked T S q _)
     rw [out]
     change ∀G,agreement T S G=true → Refines G P → q<G.length-1
     intro G hG href
     have low:=spec G hG href
     have count:=FreshOrdinaryBridge.refined_parent_count T S P G ps hG href
     omega
   | some F =>
     rw [out] at spec
     obtain ⟨hag,href,hlocal,hmin⟩:=spec
     have payment:=ActualOrdinaryExecution.literal_output_payment q T S P F ps (by omega) affordable hag href hlocal
     have check : BothBad.checked T S q (some F)=some F := by
       simp [BothBad.checked,BothBad.accept,hag]
       omega
     change RefiningQueryExact T S P q (BothBad.checked T S q _)
     rw [out]
     rw [check]
     exact ⟨hag,href,payment.2,hmin⟩
 · rw [if_neg affordable]
   refine ⟨?_,?_⟩
   · change ∀G,agreement T S G=true → Refines G P → q<G.length-1
     intro G hG href
     have count:=FreshOrdinaryBridge.refined_parent_count T S P G ps hG href
     omega
   · change ∀c,c∈([] : List BothBad.Call) → c.budget<q
     intro c hc
     cases hc
end FreshLiteralDisjoint

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshLiteralDisjoint.query_parent_contract
#print axioms FreshLiteralDisjoint.query_parent_contract
