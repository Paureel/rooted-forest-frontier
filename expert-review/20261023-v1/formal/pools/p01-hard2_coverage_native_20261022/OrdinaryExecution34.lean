import FreshCallback29
import OrdinaryBudget30
open RMAF Universal233 PaidQueries RestrictionBridge
namespace FreshOrdinaryBridge
def ParentQueryExact (T S : Tree) (Q : List (List Nat)) (b : Nat)
    (answer : Option MafScheduler.Forest) : Prop :=
  match answer with
  | none => ∀G,agreement T S G=true → Refines G Q → b<G.length-Q.length
  | some F => agreement T S F=true ∧ Refines F Q ∧ F.length-Q.length≤b ∧
      ∀G,agreement T S G=true → Refines G Q → F.length≤G.length

theorem original_call_match_budget (tx sx : Option Tree) (b : Nat) (c : BothBad.Call)
    (h : BothBad.ordinaryExecution.match_1 (fun _ _=>Option BothBad.Call) tx sx
      (fun t s=>some (BothBad.Call.mk (some t) [s] b)) (fun _ _=>none)=some c) : c.budget=b := by
  cases tx with
  | none =>
    change none=some c at h
    cases h
  | some t =>
    cases sx with
    | none =>
      change none=some c at h
      cases h
    | some s =>
      change some (BothBad.Call.mk (some t) [s] b)=some c at h
      have he:=Option.some.inj h
      exact congrArg BothBad.Call.budget he.symm

theorem prepared_calls_below (solve : BothBad.ForestSolver) (T S : Tree)
    (Q : List (List Nat)) (b outer : Nat) (js : List (Job (List Nat) MafScheduler.Forest))
    (hprepare : MafScheduler.prepare T S Q=some js) (hstrict : allocated b js<outer) :
    ∀c∈(BothBad.ordinaryExecution solve T S Q b).calls,c.budget<outer := by
  intro c hc
  unfold BothBad.ordinaryExecution at hc
  rw [hprepare] at hc
  simp only [BothBad.ordinaryExecution.match_4,BothBad.Execution.calls] at hc
  have budgets : ∀ub∈(meterSchedule (MafScheduler.recursive T S (BothBad.asTree solve)) (fun _ _=>0) b js).queries,
      ub.2=allocated b js := by
    unfold meterSchedule
    by_cases guard : b<knownCost js+2*pending js
    · rw [if_pos guard]
      intro ub hub
      exact False.elim (List.not_mem_nil hub)
    · rw [if_neg guard]
      intro ub hub
      exact (meter_queries_budget (MafScheduler.recursive T S (BothBad.asTree solve))
        (fun _ _=>0) (allocated b js) js ub hub).1
  obtain ⟨ub,hub,hcall⟩:=List.mem_filterMap.mp hc
  have budget:=budgets ub hub
  have hb:=original_call_match_budget (restrict ub.1 T) (restrict ub.1 S) ub.2 c hcall
  rw [hb,budget]
  exact hstrict

theorem execution_contract (outer b : Nat) (below : IndependentReconstruction.BelowBudget outer)
    (hb : b<outer) (T S : Tree) (Q : List (List Nat))
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q=true) (hQS : partitionCheck (leaves S) Q=true)
    (eT : pairwiseEmbeddings T Q=true) (eS : pairwiseEmbeddings S Q=true) :
    ParentQueryExact T S Q b
      (BothBad.ordinaryExecution (GenericForest.solve (IndependentReconstruction.OwnPaid outer)) T S Q b).answer ∧
    ∀c∈(BothBad.ordinaryExecution (GenericForest.solve (IndependentReconstruction.OwnPaid outer)) T S Q b).calls,
      c.budget<outer := by
  obtain ⟨t,s,ht,hs,hproper⟩:=parent_materializes T S Q pt ps hQT hQS
  obtain ⟨m,hm⟩:=parent_local_minima Q t s (fun U hU=>(hproper U hU).2)
  obtain ⟨js,hprepare,hkeys,hplan⟩:=prepare_planned_fresh T S Q t s m ht hs hproper hm
  let solve := GenericForest.solve (IndependentReconstruction.OwnPaid outer)
  let r:=allocated b js
  have strict : r<outer := by have := allocated_le b js; dsimp [r]; omega
  have localExact (U : List Nat) (hU : U∈Q) :
      OrdinaryDispatch.QueryExact (t U) (s U) r (BothBad.asTree solve (t U) (s U) r) :=
    singleton_callback_exact outer r strict below (t U) (s U) (hproper U hU).2
  have callSound : ∀U∈Q,∀F,BothBad.asTree solve (t U) (s U) r=some F →
      agreement (t U) (s U) F=true ∧ F.length-1=m U := by
    intro U hU F hF
    have exactU:=localExact U hU
    rw [hF] at exactU
    obtain ⟨M,hM,hcost⟩:=(hm U hU).1
    have lower:=(hm U hU).2 F exactU.1
    have upper:=Nat.sub_le_sub_right (exactU.2.2 M hM) 1
    exact ⟨exactU.1,by omega⟩
  have callComplete : ∀U∈Q,m U≤r → ∃F,BothBad.asTree solve (t U) (s U) r=some F := by
    intro U hU hbudget
    have exactU:=localExact U hU
    cases hF : BothBad.asTree solve (t U) (s U) r with
    | some F => exact ⟨F,rfl⟩
    | none =>
      rw [hF] at exactU
      obtain ⟨M,hM,hcost⟩:=(hm U hU).1
      have impossible:=exactU M hM
      omega
  refine ⟨?_,prepared_calls_below solve T S Q b outer js hprepare strict⟩
  change ParentQueryExact T S Q b (BothBad.ordinaryExecution solve T S Q b).answer
  cases result : (BothBad.ordinaryExecution solve T S Q b).answer with
  | none =>
    intro G hG href
    have lower:=refined_total_lower T S Q pt ps hQS t s m ht hs hm js hkeys G hG href
    by_cases feasible : G.length-Q.length≤b
    · obtain ⟨F,hF⟩:=prepared_complete solve T S Q t s m b js ht hs hprepare hkeys hplan
        callSound callComplete (by omega)
      rw [result] at hF
      cases hF
    · omega
  | some F =>
    obtain ⟨hag,href,hcost,hbudget⟩:=prepared_sound solve T S Q t s m b js pt ps hQT hQS eT eS
      ht hs hprepare hkeys hplan callSound F result
    refine ⟨hag,href,by omega,?_⟩
    intro G hG hGref
    have lower:=refined_total_lower T S Q pt ps hQS t s m ht hs hm js hkeys G hG hGref
    have count:=refined_parent_count T S Q G hQS hG hGref
    omega

theorem literal_parent_contract (outer : Nat) (below : IndependentReconstruction.BelowBudget outer)
    (T S : Tree) (Q : List (List Nat))
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q=true) (hQS : partitionCheck (leaves S) Q=true)
    (eT : pairwiseEmbeddings T Q=true) (eS : pairwiseEmbeddings S Q=true)
    (hpay : Q.length-1≤outer) (hparents : 2≤Q.length) :
    ParentQueryExact T S Q (outer-(Q.length-1))
      (BothBad.ordinaryExecution (GenericForest.solve (IndependentReconstruction.OwnPaid outer))
        T S Q (outer-(Q.length-1))).answer ∧
    ∀c∈(BothBad.ordinaryExecution (GenericForest.solve (IndependentReconstruction.OwnPaid outer))
      T S Q (outer-(Q.length-1))).calls,c.budget<outer := by
  apply execution_contract outer (outer-(Q.length-1)) below (by omega) T S Q pt ps hQT hQS eT eS

theorem literal_output_payment (outer : Nat) (T S : Tree) (Q F : List (List Nat))
    (hQS : partitionCheck (leaves S) Q=true) (hparents : 1≤Q.length)
    (hpay : Q.length-1≤outer) (hAF : agreement T S F=true) (href : Refines F Q)
    (hlocal : F.length-Q.length≤outer-(Q.length-1)) :
    F.length-1=(Q.length-1)+(F.length-Q.length) ∧ F.length-1≤outer := by
  have count:=refined_parent_count T S Q F hQS hAF href
  omega
end FreshOrdinaryBridge

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshOrdinaryBridge.original_call_match_budget
#print axioms FreshOrdinaryBridge.original_call_match_budget
#check @FreshOrdinaryBridge.prepared_calls_below
#print axioms FreshOrdinaryBridge.prepared_calls_below
#check @FreshOrdinaryBridge.execution_contract
#print axioms FreshOrdinaryBridge.execution_contract
#check @FreshOrdinaryBridge.literal_parent_contract
#print axioms FreshOrdinaryBridge.literal_parent_contract
#check @FreshOrdinaryBridge.literal_output_payment
#print axioms FreshOrdinaryBridge.literal_output_payment
