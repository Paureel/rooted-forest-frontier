import Hard2GraphSourceBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open Universal233.Hard2Overlap GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.Rule5PendantLocalWork Universal233.Rule5PrefixLocalWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration

/-- Exact remaining code site after the owned graph and disjoint tests. A paid
or Rule5 route is not an assumed unit-cost body. -/
inductive Hard2Route where
 | refused
 | direct : Option (List (List Nat))→Hard2Route
 | admittedRule5
 | disjointPaid
 | paid : Result→Hard2Route
 deriving Repr

def hard2FrontMeter (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) : Charged Hard2Route :=
 let graph:=runHard2Meter T S c
 match graph.value with
 | none=>⟨.refused,graph.work+2⟩
 | some .disjoint=>
  let p:=partitionMeter S c.a c.b
  let all:=meterAll (meterRestrictionAgrees T S) p.value
  if all.value then
   ⟨.direct (DisjointParents.direct p.value q),graph.work+p.work+all.work+p.value.length+8⟩
  else
   let good:=meterFilter (meterRestrictionAgrees T S) p.value
   ⟨if good.value.length=2 then .admittedRule5 else .disjointPaid,
     graph.work+p.work+all.work+good.work+good.value.length+8⟩
 | some out=>⟨.paid out,graph.work+4⟩

def executeHard2Route (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (q : Nat) : Hard2Route→Option (List (List Nat))
 | .refused=>none
 | .direct answer=>answer
 | .admittedRule5=>Hard2Dispatcher.rule5Answer actual T S c.a c.b q
 | .disjointPaid=>DisjointParents.run actual T S c.a c.b q
 | .paid out=>(Hard2Combine.combine actual T S c.a c.b q (Hard2Dispatcher.paidCase actual T S c q out)).answer

theorem hard2FrontMeter_value (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c d : CherryBranching.Candidate) (q : Nat) :
 executeHard2Route actual T S c q (hard2FrontMeter T S c q).value=Hard2Dispatcher.run actual T S c d q := by
 cases h:runHard2 T S c with
 | none=>simp [hard2FrontMeter,Hard2Dispatcher.run,h,executeHard2Route]
 | some out=>cases out with
  | disjoint=>
   simp only [hard2FrontMeter,runHard2Meter_value,h,partition_value,meterAll_value,meterRestrictionAgrees_value,
    meterFilter_value,Hard2Dispatcher.run]
   split <;> first | rfl | split <;> rfl
  | clique v=>simp [hard2FrontMeter,Hard2Dispatcher.run,h,executeHard2Route]
  | four o v w=>simp [hard2FrontMeter,Hard2Dispatcher.run,h,executeHard2Route]
  | diagonal o v w=>simp [hard2FrontMeter,Hard2Dispatcher.run,h,executeHard2Route]
  | pair o choice=>simp [hard2FrontMeter,Hard2Dispatcher.run,h,executeHard2Route]

/-- The route's ordinary queries are exactly those of the existing literal
hard2 trace. Unmetered remaining bodies retain their actual queries. -/
def hard2RouteQueries (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c : CherryBranching.Candidate) (q : Nat) : Hard2Route→List Query
 | .refused=>[]
 | .direct _=>[]
 | .admittedRule5=>Rule5ActualTrace.queries actual (Rule5ActualTrace.dispatchTrace actual T S c.a c.b q).calls
 | .disjointPaid=>forestQueries actual (Hard2Trace.disjointExecution actual T S c.a c.b q).calls
 | .paid out=>forestQueries actual (Hard2Combine.combine actual T S c.a c.b q (Hard2Dispatcher.paidCase actual T S c q out)).calls

theorem hard2FrontMeter_queries (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (c d : CherryBranching.Candidate) (q : Nat) :
 hard2RouteQueries actual T S c q (hard2FrontMeter T S c q).value=(hard2Trace actual T S c d q).queries := by
 cases h:runHard2 T S c with
 | none=>simp [hard2FrontMeter,hard2Trace,h,hard2RouteQueries]
 | some out=>cases out with
  | disjoint=>
   simp only [hard2FrontMeter,runHard2Meter_value,h,partition_value,meterAll_value,meterRestrictionAgrees_value,
    meterFilter_value,hard2Trace]
   split <;> first | rfl | split <;> rfl
  | clique v=>simp [hard2FrontMeter,hard2Trace,h,hard2RouteQueries]
  | four o v w=>simp [hard2FrontMeter,hard2Trace,h,hard2RouteQueries]
  | diagonal o v w=>simp [hard2FrontMeter,hard2Trace,h,hard2RouteQueries]
  | pair o choice=>simp [hard2FrontMeter,hard2Trace,h,hard2RouteQueries]

theorem partitionBudget_mono {n N : Nat} (h:n≤N) : partitionBudget n≤partitionBudget N := by
 unfold partitionBudget coreBudget pendantPayloadBudget blocksBudget payloadCap cutsBudget cutGuardBudget minimalBudget
 repeat first | exact h | exact Nat.le_refl _ | apply Nat.add_le_add | apply Nat.mul_le_mul

def hard2FrontCoefficient (N : Nat) :=partitionBudget N+2700*(N+1)^6

theorem hard2FrontMeter_bound (T S : Tree) (c : CherryBranching.Candidate) (q N : Nat)
 (three : 3≤N) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (hard2FrontMeter T S c q).work≤hard2FrontCoefficient N := by
 have sl:=Nat.le_trans (leaves_nodes S) sn
 have graph:=runHard2Meter_bound T S c N three tn sn
 have partition0:=Nat.le_trans (partition_work S c.a c.b) (partitionBudget_mono sl)
 have plen: (partitionMeter S c.a c.b).value.length≤2*N+1:=by have h:=(partition_domain S c.a c.b).1;omega
 have blocks (B : List Nat) (h:B∈(partitionMeter S c.a c.b).value) : B.length≤N:=
  Nat.le_trans (partition_block_domain S c.a c.b h).1 sl
 have point (B : List Nat) (h:B∈(partitionMeter S c.a c.b).value) :
  (meterRestrictionAgrees T S B).work≤128*(N+1)^2:=
  meterRestrictionAgrees_bound T S B N (by omega) (by omega) (blocks B h)
 have pos2:1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
 have coef:128*(N+1)^2+4≤132*(N+1)^2:=by omega
 have poly:132*(N+1)^2*((partitionMeter S c.a c.b).value.length+1)≤264*(N+1)^3:=by
  have h:=Nat.mul_le_mul_left (132*(N+1)^2) (show (partitionMeter S c.a c.b).value.length+1≤2*(N+1) by omega)
  have eq:132*(N+1)^2*(2*(N+1))=264*(N+1)^3:=by
   calc
    _=2*(132*((N+1)^2*(N+1))):=by ac_rfl
    _=2*(132*(N+1)^3):=congrArg (fun n=>2*(132*n)) (Nat.pow_succ (N+1) 2).symm
    _=264*(N+1)^3:=by omega
  rw [eq] at h
  exact h
 have a0:=meterAll_bound (meterRestrictionAgrees T S) (partitionMeter S c.a c.b).value (128*(N+1)^2) point
 have f0:=meterFilter_bound (meterRestrictionAgrees T S) (partitionMeter S c.a c.b).value (128*(N+1)^2) point
 have a:=cap_lift N 264 3 6 _ (Nat.le_trans a0 (Nat.le_trans (Nat.mul_le_mul_right _ coef) poly)) (by decide)
 have f:=cap_lift N 264 3 6 _ (Nat.le_trans f0 (Nat.le_trans (Nat.mul_le_mul_right _ coef) poly)) (by decide)
 have fl:(meterFilter (meterRestrictionAgrees T S) (partitionMeter S c.a c.b).value).value.length≤2*N+1:=by
  rw [meterFilter_value]
  exact Nat.le_trans (List.length_filter_le _ _) plen
 have pos:1≤(N+1)^6:=Nat.one_le_pow _ _ (by omega)
 have np:N+1≤(N+1)^6:=by simpa only [Nat.pow_one] using pow_mono N 1 6 (by decide)
 cases h:(runHard2Meter T S c).value with
 | none=>simp only [hard2FrontMeter,h,hard2FrontCoefficient];omega
 | some out=>
  cases out <;> simp only [hard2FrontMeter,h,hard2FrontCoefficient]
  all_goals first | omega | split <;> simp only [Charged.work] <;> omega
end OrdinaryDispatch.Hard2SourceWork
