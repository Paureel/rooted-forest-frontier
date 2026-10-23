import DisjointParentSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork SourceCoverage
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Universal233.BothBad Universal233.PaidQueries
open OrdinaryDispatch.WorkIntegration OrdinaryDispatch.FullSourceWork
open OrdinaryDispatch.WorkRecursion

def disjointQueryPolynomial (N L : Nat):=
 ordinaryLocalPolynomial N L+agreementK (ordinaryCheckSize N L)+N*L+L+24
theorem disjointQueryLocalSource_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (parts : List (List Nat)) (q N : Nat) (three:3≤N)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (blocks:∀U,U∈parts→U.length≤N) :
 (disjointQueryLocalSource actual T S parts q).work≤disjointQueryPolynomial N parts.length:=by
 have localBill:=ordinaryLocalSource_bound actual T S parts (q-(parts.length-1)) N three tn sn blocks
 have check:=ordinary_checked_bound actual T S parts (q-(parts.length-1)) q N three tn sn
 simp only [disjointQueryLocalSource,disjointQueryPolynomial,ordinaryLocalSource_value]
 split <;> dsimp only <;> omega

theorem disjoint_query_proper (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (parts : List (List Nat)) (q : Nat) (a : Call)
 (mem:a∈(OrdinaryDispatch.DisjointParents.query actual T S parts q).calls) : proper a.target a.sources=true:=by
 unfold OrdinaryDispatch.DisjointParents.query at mem
 split at mem
 · exact ordinary_execution_queries_proper (GenericForest.solve actual) T S parts _ a mem
 · simp at mem
theorem disjoint_query_labels (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (parts : List (List Nat)) (q N : Nat) (tn:treeNodes T≤N) (a : Call)
 (mem:a∈(OrdinaryDispatch.DisjointParents.query actual T S parts q).calls) : (labels a.target).length≤N:=by
 unfold OrdinaryDispatch.DisjointParents.query at mem
 split at mem
 · exact ordinary_call_labels actual T S parts _ N tn a mem
 · simp at mem
theorem disjoint_query_budget (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (parts : List (List Nat)) (q : Nat) (a : Call)
 (mem:a∈(OrdinaryDispatch.DisjointParents.query actual T S parts q).calls) : a.budget≤q:=by
 unfold OrdinaryDispatch.DisjointParents.query at mem
 split at mem
 · have cap:=ordinary_budget_cap (GenericForest.solve actual) T S parts _ a mem;omega
 · simp at mem

/-- At the literal three-parent, two-bad-parent domain, the checked scheduler
cost has the sharp c^-3 forest coefficient. No source-cost premise is supplied. -/
theorem disjointQuerySource_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (parts : List (List Nat)) (q N Q : Nat) (three:3≤N) (budget:q≤Q)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (blocks:∀U,U∈parts→U.length≤N)
 (count:parts.length=3) (bad:2≤MafScheduler.badParents T S parts) :
 ((disjointQuerySource actual (fun _ _ _=>0) T S parts q).work:Rat)≤
 ((disjointQueryPolynomial N parts.length:Rat)+geometric Rule5ActualTrace.base*forestCoefficient N Q*
 Rule5ActualTrace.base^(-3:Int))*Rule5ActualTrace.base^q:=by
 have localBill:=disjointQueryLocalSource_bound actual T S parts q N three tn sn blocks
 have debit:=callsForestDebit_weighted actual (OrdinaryDispatch.DisjointParents.query actual T S parts q).calls q N Q budget
  (disjoint_query_proper actual T S parts q) (disjoint_query_labels actual T S parts q N tn)
  (disjoint_query_budget actual T S parts q)
 have mass:=OrdinaryDispatch.DisjointParents.query_mass actual T S parts q count bad Rule5ActualTrace.base (by decide +kernel)
 have positive:0≤geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^q:=
  Rat.mul_nonneg (Rat.mul_nonneg (geometric_properties _ (by decide +kernel)).2.2.1 Rat.natCast_nonneg)
   (Rat.le_of_lt (Rat.pow_pos (by decide +kernel)))
 have weighted:=Rat.le_trans debit (Rat.mul_le_mul_of_nonneg_left mass positive)
 have regroup:(geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^q)*Rule5ActualTrace.base^(-3:Int)=
  (geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^(-3:Int))*Rule5ActualTrace.base^q:=by
  rw [Rat.mul_assoc,Rat.mul_comm (Rule5ActualTrace.base^q) (Rule5ActualTrace.base^(-3:Int)),←Rat.mul_assoc]
 rw [regroup] at weighted
 have localPow:=Rat.mul_le_mul_of_nonneg_left (call_base_pow_ge_one q)
  (show 0≤(disjointQueryPolynomial N parts.length:Rat) from Rat.natCast_nonneg)
 rw [Rat.mul_one] at localPow
 have total:=qadd_le_add (Rat.le_trans (Rat.natCast_le_natCast.2 localBill) localPow) weighted
 simpa only [disjointQuerySource,disjointQueryLocalSource_value,Rat.natCast_add,Rat.add_mul] using total
end OrdinaryDispatch.Hard2SourceWork
