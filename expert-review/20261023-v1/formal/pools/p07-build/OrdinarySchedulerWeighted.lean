import OrdinarySchedulerBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork SourceCoverage
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion OrdinaryDispatch.FullSourceWork
open Universal233.BothBad Universal233.PaidQueries

theorem ordinary_call_labels (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (Q : List (List Nat)) (b N : Nat) (tn:treeNodes T≤N)
 (a : Call) (mem:a∈(ordinaryExecution (GenericForest.solve actual) T S Q b).calls) :
 (labels a.target).length≤N:=by
 cases prep:MafScheduler.prepare T S Q with
 | none=>simp only [ordinaryExecution,prep,List.not_mem_nil] at mem
 | some js=>
   simp only [ordinaryExecution,prep] at mem
   obtain ⟨ub,_,hm⟩:=List.mem_filterMap.1 mem
   cases ht:restrict ub.1 T with
   | none=>simp [ht] at hm
   | some t=>cases hs:restrict ub.1 S with
     | none=>simp [ht,hs] at hm
     | some s=>
       have eq:(⟨some t,[s],ub.2⟩:Call)=a:=by simpa only [ht,hs,Option.some.injEq] using hm
       subst a
       exact Nat.le_trans (leaves_nodes t) (Nat.le_trans (restricted_nodes ub.1 T t ht) tn)

/-- The sharp ordinary handler bound keeps its actual trace mass. No maximum
local exponential bill is multiplied by an unweighted total call count. -/
theorem ordinarySource_trace_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (parts : List (List Nat)) (b N Q : Nat) (three:3≤N) (budget:b≤Q)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (blocks:∀U,U∈parts→U.length≤N) :
 ((ordinarySource actual (fun _ _ _=>0) T S parts b).work:Rat)≤
 (ordinaryLocalPolynomial N parts.length:Rat)+
 (geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^b)*
 traceMass Rule5ActualTrace.base b (ordinaryExecution (GenericForest.solve actual) T S parts b).calls:=by
 have localBill:=Rat.natCast_le_natCast.2 (ordinaryLocalSource_bound actual T S parts b N three tn sn blocks)
 have debit:=callsForestDebit_weighted actual (ordinaryExecution (GenericForest.solve actual) T S parts b).calls b N Q budget
  (ordinary_execution_queries_proper (GenericForest.solve actual) T S parts b)
  (ordinary_call_labels actual T S parts b N tn)
  (ordinary_budget_cap (GenericForest.solve actual) T S parts b)
 have total:=qadd_le_add localBill debit
 simpa only [ordinarySource,ordinaryLocalSource_value,Rat.natCast_add] using total

theorem ordinarySource_uniform_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (parts : List (List Nat)) (b N Q : Nat) (three:3≤N) (budget:b≤Q)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (blocks:∀U,U∈parts→U.length≤N) :
 ((ordinarySource actual (fun _ _ _=>0) T S parts b).work:Rat)≤
 ((ordinaryLocalPolynomial N parts.length:Rat)+geometric Rule5ActualTrace.base*forestCoefficient N Q)*Rule5ActualTrace.base^b:=by
 have h:=ordinarySource_trace_bound actual T S parts b N Q three budget tn sn blocks
 have mass:=ordinary_mass_one (GenericForest.solve actual) T S parts b Rule5ActualTrace.base (by decide +kernel)
 have nonneg:0≤geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^b:=
  Rat.mul_nonneg (Rat.mul_nonneg (geometric_properties _ (by decide +kernel)).2.2.1 Rat.natCast_nonneg)
   (Rat.le_of_lt (Rat.pow_pos (by decide +kernel)))
 have debit:=Rat.mul_le_mul_of_nonneg_left mass nonneg
 rw [Rat.mul_one] at debit
 have localPow:=Rat.mul_le_mul_of_nonneg_left (call_base_pow_ge_one b)
  (show 0≤(ordinaryLocalPolynomial N parts.length:Rat) from Rat.natCast_nonneg)
 rw [Rat.mul_one] at localPow
 exact Rat.le_trans h (by simpa only [Rat.add_mul] using qadd_le_add localPow debit)
end OrdinaryDispatch.Hard2SourceWork
