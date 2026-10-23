import Hard2StepTrace
namespace OrdinaryDispatch.WorkIntegration
open RMAF ForestState Universal233 Universal233.BothBad Universal233.PaidQueries Universal233.SourceCoverage
open Universal233.CherryBranching Universal233.Hard2Overlap
open OrdinaryDispatch.Hard2Dispatcher GenericForest.FrontierWork

def BelowWorkBill (W : OrdinaryWork) (N q : Nat) (c D : Rat) : Prop :=
 ∀t s r,DepthOne.proper t s=true→(leaves t).length≤N→(leaves s).length≤N→r<q→(W t s r:Rat)≤D*c^r

def forestCoefficient (N q : Nat) : Rat := ((2^50*(N+q+2)^8:Nat):Rat)

theorem forest_call_source_bound (actual : Ordinary) (W : OrdinaryWork) (N q : Nat) (c D : Rat)
 (base : 2<c) (positive : 0≤D) (bill : BelowWorkBill W N q c D) (call : Call)
 (proper0 : proper call.target call.sources=true) (size : (labels call.target).length≤N) (strict : call.budget<q) :
 GenericForest.sourceWork actual W call.target call.sources call.budget≤
 (D+geometric c*forestCoefficient N q)*c^call.budget := by
 apply GenericForest.FrontierSize.source_work_bound_on_queries actual W call.target q c _ D base
  Rat.natCast_nonneg positive
  (GenericForest.LocalPolynomial.monomial_local_overhead actual call.target N q c (Rat.le_of_lt base) size)
  call.sources call.budget (Nat.le_of_lt strict) proper0
 intro p r mem
 have valid := frontier_queries_proper actual call.target call.sources call.budget proper0 p r mem
 have sizes := GenericForest.FrontierSize.frontier_query_size actual call.target call.sources call.budget proper0 p r mem
 exact bill p.1 p.2 r valid.2 (Nat.le_trans sizes.1 size) (Nat.le_trans sizes.2 size)
  (Nat.lt_of_le_of_lt valid.1 strict)

theorem call_power_sum (calls : List Call) (c : Rat) (positive : 0<c) (q : Nat)
 (budgets : ∀call,call∈calls→call.budget≤q) :
 (calls.map fun call=>c^call.budget).sum=c^q*traceMass c q calls := by
 have point (call : Call) (mem : call∈calls) : c^call.budget=c^q*c^(-((q-call.budget:Nat):Int)) := by
  have budget := budgets call mem
  have h := qpow_clear c (Rat.ne_of_gt positive) q (q-call.budget) (by omega)
  simpa only [Nat.sub_sub_self budget] using h
 have eq := List.map_congr_left point
 rw [eq,GenericForest.rat_sum_mul]
 simp only [traceMass,actualQueryMass,List.map_map,Function.comp_def]

theorem forest_calls_source_bound (actual : Ordinary) (W : OrdinaryWork) (N q : Nat) (c D : Rat)
 (base : 2<c) (positive : 0≤D) (bill : BelowWorkBill W N q c D) (calls : List Call)
 (proper0 : ∀call,call∈calls→proper call.target call.sources=true)
 (sizes : ∀call,call∈calls→(labels call.target).length≤N)
 (strict : ∀call,call∈calls→call.budget<q) :
 (calls.map fun call=>GenericForest.sourceWork actual W call.target call.sources call.budget).sum≤
 (D+geometric c*forestCoefficient N q)*c^q*traceMass c q calls := by
 have sum := GenericForest.rat_sum_map_le calls
  (fun call=>GenericForest.sourceWork actual W call.target call.sources call.budget)
  (fun call=>(D+geometric c*forestCoefficient N q)*c^call.budget)
  (fun call hc=>forest_call_source_bound actual W N q c D base positive bill call (proper0 call hc) (sizes call hc) (strict call hc))
 rw [GenericForest.rat_sum_mul,call_power_sum calls c (by grind : 0<c) q (fun call hc=>Nat.le_of_lt (strict call hc))] at sum
 simpa only [Rat.mul_assoc] using sum

theorem combined_source_bill_bound (actual : Ordinary) (W : OrdinaryWork) {T S : Tree}
 {c : Candidate} {q : Nat} {out : Result}
 (proper0 : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (selected : runHard2 T S c=some out) (b D : Rat) (base : 2<b) (upper : b≤3) (positive : 0≤D)
 (bill : BelowWorkBill W (leaves T).length q b D) :
 ((Hard2Combine.combine actual T S c.a c.b q (paidCase actual T S c q out)).calls.map
  fun call=>GenericForest.sourceWork actual W call.target call.sources call.budget).sum≤
 (D+geometric b*forestCoefficient (leaves T).length q)*b^q*(2*b^(-1 : Int)+4*b^(-4 : Int)) := by
 have sum := forest_calls_source_bound actual W (leaves T).length q b D base positive bill _
  (fun call hc=>combined_queries_proper actual proper0 hard selected call hc)
  (fun call hc=>(Hard2Size.combined_target_bound actual T S c q out call hc).2)
  (fun call hc=>Hard2Trace.combined_calls_strict actual proper0 hard selected call hc)
 have mass := Hard2Trace.combined_mass (q:=q) actual proper0 hard selected b (Rat.le_of_lt base) upper
 have coeff : 0≤(D+geometric b*forestCoefficient (leaves T).length q)*b^q :=
  Rat.mul_nonneg (Rat.add_nonneg positive (Rat.mul_nonneg (geometric_properties b base).2.2.1 Rat.natCast_nonneg))
   (Rat.le_of_lt (Rat.pow_pos (by grind : 0<b)))
 exact Rat.le_trans sum (Rat.mul_le_mul_of_nonneg_left mass coeff)

theorem disjoint_source_bill_bound (actual : Ordinary) (W : OrdinaryWork) {T S : Tree}
 {c : Candidate} (q : Nat) (proper0 : DepthOne.proper T S=true)
 (hard : CherryBranching.select T S=some (.hard2,c))
 (notAll : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false)
 (notTwo : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length≠2)
 (b D : Rat) (base : 2<b) (upper : b≤3) (positive : 0≤D)
 (bill : BelowWorkBill W (leaves T).length q b D) :
 ((Hard2Trace.disjointExecution actual T S c.a c.b q).calls.map
  fun call=>GenericForest.sourceWork actual W call.target call.sources call.budget).sum≤
 (D+geometric b*forestCoefficient (leaves T).length q)*b^q*(2*b^(-1 : Int)+4*b^(-4 : Int)) := by
 have sum := forest_calls_source_bound actual W (leaves T).length q b D base positive bill _
  (fun call hc=>disjoint_queries_proper actual q proper0 hard call hc)
  (fun call hc=>(Hard2Size.disjoint_target_bound actual T S c.a c.b q call hc).2)
  (fun call hc=>Hard2Trace.disjointExecution_strict actual q proper0 hard call hc)
 have mass := Hard2Trace.disjointExecution_mass actual q proper0 hard notAll notTwo b (Rat.le_of_lt base) upper
 have coeff : 0≤(D+geometric b*forestCoefficient (leaves T).length q)*b^q :=
  Rat.mul_nonneg (Rat.add_nonneg positive (Rat.mul_nonneg (geometric_properties b base).2.2.1 Rat.natCast_nonneg))
   (Rat.le_of_lt (Rat.pow_pos (by grind : 0<b)))
 exact Rat.le_trans sum (Rat.mul_le_mul_of_nonneg_left mass coeff)

/-- Conditional recursive ordinary charge is paid once across the complete
actual hard2 frontier; all local source work remains explicitly separate. -/
theorem hard2_ordinary_work_bound (actual : Ordinary) (W : OrdinaryWork) {T S : Tree} {c d : Candidate} (q : Nat)
 (proper0 : DepthOne.proper T S=true)
 (forward : CherryBranching.select T S=some (.hard2,c))
 (reverse : CherryBranching.select S T=some (.hard2,d))
 (noT : Rule4.select T S=none) (noS : Rule4.select S T=none) (D : Rat) (positive : 0≤D)
 (bill : BelowWorkBill W (leaves T).length q Rule5ActualTrace.base D) :
 (queryWork W (hard2Trace actual T S c d q).queries:Rat)≤D*Rule5ActualTrace.base^q*Rule5ActualTrace.gamma Rule5ActualTrace.base := by
 let xs := (hard2Trace actual T S c d q).queries
 have point (pb : Query) (mem : pb∈xs) : (W pb.1.1 pb.1.2 pb.2:Rat)≤D*Rule5ActualTrace.base^pb.2 := by
  have b := hard2Trace_query_bounds actual q proper0 forward reverse noT noS pb.1 pb.2 mem
  exact bill pb.1.1 pb.1.2 pb.2 b.2.1 b.2.2.1 b.2.2.2 b.1
 have sum := GenericForest.rat_sum_map_le xs
  (fun pb=>(W pb.1.1 pb.1.2 pb.2:Rat)) (fun pb=>D*Rule5ActualTrace.base^pb.2) point
 rw [GenericForest.rat_sum_mul] at sum
 have power := frontierPower_as_mass Rule5ActualTrace.base (by cbv : 0<Rule5ActualTrace.base) q xs
  (fun p r mem=>Nat.le_of_lt (hard2Trace_query_bounds actual q proper0 forward reverse noT noS p r mem).1)
 change _≤D*frontierPower Rule5ActualTrace.base xs at sum
 rw [power] at sum
 have mass := hard2Trace_mass actual q proper0 forward reverse noT noS
 have scalePos : (0 : Rat)≤D*Rule5ActualTrace.base^q :=
  Rat.mul_nonneg positive (Rat.le_of_lt (Rat.pow_pos (by cbv : 0<Rule5ActualTrace.base)))
 have scale := Rat.mul_le_mul_of_nonneg_left mass scalePos
 rw [queryWork_cast]
 exact Rat.le_trans sum (by simpa only [Rat.mul_assoc,xs,Rule5ActualTrace.mass] using scale)
end OrdinaryDispatch.WorkIntegration
