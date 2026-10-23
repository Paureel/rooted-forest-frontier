import Hard2RouteTraceV3
import Hard2WholeSourceExecutionV3
import DisjointSlotRealizationV3

namespace SourceHard2WholeV3
open RMAF Universal233 SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)

abbrev Occurrence := SourcePaidUnitsV3.Occurrence
def linear (slots : List SourceForestV3.S) : List Occurrence :=
  slots.map (fun s=>((false,(0,s.index)),s))

-- These constructors fix the chronological ledger from the executed branch graph.
-- In particular paid uses its existing paid-before-units chronological ledger.
inductive RouteLedger (OrdExec : Tree→Tree→Nat→Option F→Prop)
    (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) :
    Hard2Route→WholeSourceWork.Charged (Option F)→List Occurrence→List Occurrence→Prop
  | refused : RouteLedger OrdExec T S c q .refused ⟨none,0⟩ [] []
  | direct (a : Option F) : RouteLedger OrdExec T S c q (.direct a) ⟨a,0⟩ [] []
  | disjoint (execution : SourceDisjointRunV3.DisjointExec OrdExec (.cutoff q)
      T S c.a c.b q r calls slots) :
      RouteLedger OrdExec T S c q .disjointPaid r (linear slots) (linear slots)
  | paid (execution : SourcePaidUnitsV3.PaidUnitsExec OrdExec (.cutoff q)
      T S c q out r rec chrono) :
      RouteLedger OrdExec T S c q (.paid out) r rec chrono
  | admitted (execution : SourceRule5DispatchV3.DispatchExec OrdExec (.cutoff q)
      T S c.a c.b q 0 r slots) :
      RouteLedger OrdExec T S c q .admittedRule5 (SourceRule5DispatchV3.answerView r)
        (linear slots) (linear slots)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem route_ledger_exists (h : RouteExec OrdExec T S c q route r) :
    ∃ rec chrono,RouteLedger OrdExec T S c q route r rec chrono := by
  cases h with
  | other execution =>
    cases execution with
    | refused => exact ⟨_,_,RouteLedger.refused⟩
    | direct a => exact ⟨_,_,RouteLedger.direct a⟩
    | disjoint execution => exact ⟨_,_,RouteLedger.disjoint execution⟩
    | paid execution => exact ⟨_,_,RouteLedger.paid execution⟩
  | admitted execution => exact ⟨_,_,RouteLedger.admitted execution⟩

theorem linear_queries {slots : List SourceForestV3.S} {qs : List Q}
    (hi : slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom 0 qs) :
    (linear slots).map (fun o=>o.2.query)=qs := by
  have hv:=congrArg (List.map Prod.snd) hi
  simpa only [linear,List.map_map,Function.comp_def,CallbackPairingAuthor.indexFrom_project] using hv

theorem linear_distinct {slots : List SourceForestV3.S} {qs : List Q}
    (hi : slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom 0 qs) :
    (linear slots).Pairwise (fun a b=>a.1≠b.1) := by
  simp only [linear,List.pairwise_map]
  exact (ledger_strict hi).imp (fun h he=>by
    have hx:=congrArg (fun x=>x.2.2) he
    dsimp at hx
    omega)

theorem linear_realizes {mode : Mode} {slots : List SourceForestV3.S}
    (hr : ∀ s∈slots,SlotRealizes OrdExec mode s) :
    ∀ o∈linear slots,SlotRealizes OrdExec mode o.2 := by
  intro o ho
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ho
  exact hr s hs

theorem route_ledger_correspondence
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : RouteLedger OrdExec T S c q route r rec chrono) :
    r.value=(SourceHard2TraceV3.routeTrace (ordinarySpec (.cutoff q) base) T S c q route).value ∧
    chrono.Perm rec ∧ rec.Pairwise (fun a b=>a.1≠b.1) ∧
    rec.map (fun o=>o.2.query)=
      (SourceHard2TraceV3.routeTrace (ordinarySpec (.cutoff q) base) T S c q route).queries ∧
    ∀ o∈rec,SlotRealizes OrdExec (.cutoff q) o.2 := by
  cases h with
  | refused => exact ⟨rfl,List.Perm.refl _,by simp,rfl,by simp⟩
  | direct a => exact ⟨rfl,List.Perm.refl _,by simp,rfl,by simp⟩
  | disjoint execution =>
    have hv:=SourceDisjointRunV3.disjoint_raw_trace sound execution
    have hi:=SourceDisjointRunV3.disjoint_trace_index sound execution
    exact ⟨hv.1,List.Perm.refl _,linear_distinct hi,linear_queries hi,
      linear_realizes (SourceDisjointRunV3.disjoint_slots_realize execution)⟩
  | paid execution =>
    exact ⟨SourcePaidUnitsV3.paid_units_raw_value sound execution,
      SourcePaidUnitsV3.paid_units_permutation execution,
      SourcePaidUnitsV3.paid_units_distinct sound execution,
      SourcePaidUnitsV3.paid_units_raw_queries sound execution,
      SourcePaidUnitsV3.paid_units_slots_realize execution⟩
  | admitted execution =>
    have hv:=SourceRule5DispatchV3.dispatch_answer_actual_trace sound execution
    exact ⟨hv.1,List.Perm.refl _,linear_distinct hv.2,linear_queries hv.2,
      linear_realizes (SourceRule5DispatchV3.dispatch_slots_realize execution)⟩

theorem route_canonical_value
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : RouteExec OrdExec T S c q route r) :
    r.value=executeHard2Route (ordinarySpec (.cutoff q) base) T S c q route := by
  cases h with
  | admitted execution => exact SourceRule5DispatchV3.dispatch_canonical_value sound execution
  | other execution =>
    cases execution with
    | refused => rfl
    | direct a => rfl
    | disjoint execution => exact SourceDisjointRunV3.disjoint_raw_value sound execution
    | paid execution => exact SourcePaidUnitsV3.paid_units_raw_value sound execution

theorem hard2_canonical_value
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Hard2Exec OrdExec T S c q r) (d : CherryBranching.Candidate) :
    r.value=OrdinaryDispatch.Hard2Dispatcher.run (ordinarySpec (.cutoff q) base) T S c d q := by
  cases h with
  | run execution =>
    have hv:=route_canonical_value sound execution
    rw [hard2FrontMeter_value _ _ _ _ d] at hv
    exact hv

theorem hard2_trace_ledger
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Hard2Exec OrdExec T S c q r) (d : CherryBranching.Candidate) :
    ∃ pr rec chrono,
      RouteLedger OrdExec T S c q (hard2FrontMeter T S c q).value pr rec chrono ∧
      r.value=(hard2Trace (ordinarySpec (.cutoff q) base) T S c d q).value ∧
      chrono.Perm rec ∧ rec.Pairwise (fun a b=>a.1≠b.1) ∧
      rec.map (fun o=>o.2.query)=(hard2Trace (ordinarySpec (.cutoff q) base) T S c d q).queries ∧
      ∀ o∈rec,SlotRealizes OrdExec (.cutoff q) o.2 := by
  cases h with
  | run execution =>
    obtain ⟨rec,chrono,ledger⟩:=route_ledger_exists execution
    have hv:=route_ledger_correspondence sound ledger
    rw [SourceHard2TraceV3.frontend_trace_cases _ _ _ _ d] at hv
    exact ⟨_,rec,chrono,ledger,hv⟩
end SourceHard2WholeV3
