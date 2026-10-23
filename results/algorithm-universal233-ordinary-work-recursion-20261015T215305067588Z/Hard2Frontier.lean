import Hard2QueryProper
import WorkComponentsV2
namespace OrdinaryDispatch.WorkIntegration
open RMAF ForestState Universal233 Universal233.BothBad Universal233.PaidQueries
open Universal233.CherryBranching Universal233.Hard2Overlap
open OrdinaryDispatch.Hard2Dispatcher GenericForest.FrontierWork

def forestQueries (actual : Ordinary) (calls : List Call) : List Query :=
 calls.flatMap fun call=>frontier actual call.target call.sources call.budget

theorem forest_queries_mass (actual : Ordinary) (q : Nat) (calls : List Call) (b : Rat) (base : 2≤b)
 (proper0 : ∀call,call∈calls→proper call.target call.sources=true)
 (caps : ∀call,call∈calls→call.budget≤q) :
 Rule5ActualTrace.mass b q (forestQueries actual calls)≤traceMass b q calls := by
 rw [forestQueries,Rule5ActualTrace.mass_flatMap]
 have bound := GenericForest.rat_sum_map_le calls
  (fun call=>Rule5ActualTrace.mass b q (frontier actual call.target call.sources call.budget))
  (fun call=>Rule5ActualTrace.debit b (q-call.budget))
  (fun call hc=>Rule5ActualTrace.forest_mass_paid actual call.target call.sources (caps call hc) (proper0 call hc) b base)
 simpa [traceMass,actualQueryMass,Rule5ActualTrace.debit,List.map_map,Function.comp_def] using bound

theorem forest_queries_bounds (actual : Ordinary) (T : Tree) (q : Nat) (calls : List Call)
 (proper0 : ∀call,call∈calls→proper call.target call.sources=true)
 (sizes : ∀call,call∈calls→(labels call.target).length≤(leaves T).length)
 (strict : ∀call,call∈calls→call.budget<q) (p : Tree×Tree) (r : Nat)
 (mem : (p,r)∈forestQueries actual calls) :
 r<q ∧ DepthOne.proper p.1 p.2=true ∧
 (leaves p.1).length≤(leaves T).length ∧ (leaves p.2).length≤(leaves T).length := by
 obtain ⟨call,hcall,inner⟩ := List.mem_flatMap.1 mem
 have valid := frontier_queries_proper actual call.target call.sources call.budget (proper0 call hcall) p r inner
 have bound := GenericForest.FrontierSize.frontier_query_size actual call.target call.sources call.budget (proper0 call hcall) p r inner
 exact ⟨Nat.lt_of_le_of_lt valid.1 (strict call hcall),valid.2,
  Nat.le_trans bound.1 (sizes call hcall),Nat.le_trans bound.2 (sizes call hcall)⟩

theorem combined_frontier_mass (actual : Ordinary) {T S : Tree} {c : Candidate} {q : Nat} {out : Result}
 (proper0 : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (selected : runHard2 T S c=some out) (b : Rat) (base : 2≤b) (upper : b≤3) :
 Rule5ActualTrace.mass b q (forestQueries actual (Hard2Combine.combine actual T S c.a c.b q (paidCase actual T S c q out)).calls)
 ≤2*b^(-1 : Int)+4*b^(-4 : Int) := by
 have inherit := forest_queries_mass actual q _ b base
  (fun call hc=>combined_queries_proper actual proper0 hard selected call hc)
  (fun call hc=>Nat.le_of_lt (Hard2Trace.combined_calls_strict actual proper0 hard selected call hc))
 exact Rat.le_trans inherit (Hard2Trace.combined_mass actual proper0 hard selected b base upper)

theorem combined_frontier_bounds (actual : Ordinary) {T S : Tree} {c : Candidate} {q : Nat} {out : Result}
 (proper0 : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (selected : runHard2 T S c=some out) (p : Tree×Tree) (r : Nat)
 (mem : (p,r)∈forestQueries actual (Hard2Combine.combine actual T S c.a c.b q (paidCase actual T S c q out)).calls) :
 r<q ∧ DepthOne.proper p.1 p.2=true ∧
 (leaves p.1).length≤(leaves T).length ∧ (leaves p.2).length≤(leaves T).length :=
 forest_queries_bounds actual T q _
  (fun call hc=>combined_queries_proper actual proper0 hard selected call hc)
  (fun call hc=>(Hard2Size.combined_target_bound actual T S c q out call hc).2)
  (fun call hc=>Hard2Trace.combined_calls_strict actual proper0 hard selected call hc) p r mem

theorem disjoint_frontier_mass (actual : Ordinary) {T S : Tree} {c : Candidate} (q : Nat)
 (proper0 : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (notAll : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false)
 (notTwo : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length≠2)
 (b : Rat) (base : 2≤b) (upper : b≤3) :
 Rule5ActualTrace.mass b q (forestQueries actual (Hard2Trace.disjointExecution actual T S c.a c.b q).calls)
 ≤2*b^(-1 : Int)+4*b^(-4 : Int) := by
 have inherit := forest_queries_mass actual q _ b base
  (fun call hc=>disjoint_queries_proper actual q proper0 hard call hc)
  (fun call hc=>Nat.le_of_lt (Hard2Trace.disjointExecution_strict actual q proper0 hard call hc))
 exact Rat.le_trans inherit (Hard2Trace.disjointExecution_mass actual q proper0 hard notAll notTwo b base upper)

theorem disjoint_frontier_bounds (actual : Ordinary) {T S : Tree} {c : Candidate} (q : Nat)
 (proper0 : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (p : Tree×Tree) (r : Nat)
 (mem : (p,r)∈forestQueries actual (Hard2Trace.disjointExecution actual T S c.a c.b q).calls) :
 r<q ∧ DepthOne.proper p.1 p.2=true ∧
 (leaves p.1).length≤(leaves T).length ∧ (leaves p.2).length≤(leaves T).length :=
 forest_queries_bounds actual T q _
  (fun call hc=>disjoint_queries_proper actual q proper0 hard call hc)
  (fun call hc=>(Hard2Size.disjoint_target_bound actual T S c.a c.b q call hc).2)
  (fun call hc=>Hard2Trace.disjointExecution_strict actual q proper0 hard call hc) p r mem
end OrdinaryDispatch.WorkIntegration
