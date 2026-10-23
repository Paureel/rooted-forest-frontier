import AffordableCalls
namespace OrdinaryDispatch.WorkRecursion
open RMAF ForestState Universal233 Universal233.BothBad
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration

def rule4Calls {T S : Tree} (s : Rule4.Choice T S) (q : Nat) : List Call :=
 affordableCalls (Rule4.branches s) Rule4.Branch.target Rule4.Branch.sourceForest Rule4.Branch.cost q

def rule4Trace (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree} (s : Rule4.Choice T S) (q : Nat) : Hard2Receipt :=
 ⟨OrdinaryDispatch.runRule4 actual s q,forestQueries actual (rule4Calls s q)⟩

theorem rule4_answers_binding (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree} (s : Rule4.Choice T S) (q : Nat) :
 Rule4.outputs s q (OrdinaryDispatch.rule4Child actual)=
 (rule4Calls s q).filterMap (fun call=>GenericForest.solve actual call.target call.sources call.budget) := by
 simpa only [rule4Calls,Rule4.outputs,Rule4.childOutputs,OrdinaryDispatch.rule4Child] using
  affordableCalls_answers (Rule4.branches s) Rule4.Branch.target Rule4.Branch.sourceForest Rule4.Branch.cost q actual

theorem rule4Trace_value (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree} (s : Rule4.Choice T S) (q : Nat) :
 (rule4Trace actual s q).value=OrdinaryDispatch.runRule4 actual s q := rfl

theorem rule4_call_facts {T S : Tree} (s : Rule4.Choice T S) (q : Nat) (call : Call) (mem : call∈rule4Calls s q) :
 proper call.target call.sources=true ∧ (labels call.target).length≤(leaves T).length ∧ call.budget<q := by
 obtain ⟨b,hb,pay,eq⟩ := affordableCalls_member (Rule4.branches s) Rule4.Branch.target Rule4.Branch.sourceForest Rule4.Branch.cost q call mem
 subst call
 have facts := Rule4.selected_source_state s b hb []
 have drop := Rule4.actual_callback_decrease s q b hb pay
 refine ⟨facts.2.2.2.2.1,?_,drop⟩
 have len := s.priority.2.2.1.length_eq
 simp only [Rule4.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
 rcases hb with rfl|rfl|rfl <;> simp only [labels] <;> omega

theorem rule4Trace_bounds (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree} (s : Rule4.Choice T S) (q : Nat)
 (p : Tree×Tree) (r : Nat) (mem : (p,r)∈(rule4Trace actual s q).queries) :
 r<q ∧ DepthOne.proper p.1 p.2=true ∧ (leaves p.1).length≤(leaves T).length ∧ (leaves p.2).length≤(leaves T).length :=
 forest_queries_bounds actual T q (rule4Calls s q)
  (fun call hm=>(rule4_call_facts s q call hm).1)
  (fun call hm=>(rule4_call_facts s q call hm).2.1)
  (fun call hm=>(rule4_call_facts s q call hm).2.2) p r mem

theorem rule4Trace_mass (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree} (s : Rule4.Choice T S) (q : Nat) :
 Rule5ActualTrace.mass Rule5ActualTrace.base q (rule4Trace actual s q).queries≤Rule5ActualTrace.gamma Rule5ActualTrace.base := by
 have inner := forest_queries_mass actual q (rule4Calls s q) Rule5ActualTrace.base (by cbv)
  (fun call hm=>(rule4_call_facts s q call hm).1)
  (fun call hm=>Nat.le_of_lt (rule4_call_facts s q call hm).2.2)
 have outer := Rule4.actual_callback_mass s q Rule5ActualTrace.base (by cbv)
 rw [←affordableCalls_mass (Rule4.branches s) Rule4.Branch.target Rule4.Branch.sourceForest Rule4.Branch.cost q Rule5ActualTrace.base] at outer
 exact Rat.le_trans inner (Rat.le_trans outer (by cbv : Rule5ActualTrace.base^(-1:Int)+2*Rule5ActualTrace.base^(-2:Int)≤Rule5ActualTrace.gamma Rule5ActualTrace.base))
end OrdinaryDispatch.WorkRecursion
