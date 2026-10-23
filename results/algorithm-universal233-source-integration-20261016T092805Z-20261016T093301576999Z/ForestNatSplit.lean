import ForestNatWork
namespace OrdinaryDispatch.WorkRecursion
open RMAF ForestState Universal233 Universal233.CoreProgram Universal233.PaidQueries Universal233.SourceCoverage
open GenericForest GenericForest.FrontierWork

theorem forestWork_split (ordinary : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (q : Nat) :
 forestWork ordinary W T ss q=forestWork ordinary (fun _ _ _=>0) T ss q+queryWork W (frontier ordinary T ss q) := by
 apply Rat.natCast_inj.1
 rw [Rat.natCast_add,forestWork_cast,forestWork_cast,queryWork_cast]
 exact source_work_split ordinary W T ss q

theorem forestLocalWork_bound (ordinary : Ordinary) (T : Option Tree) (N Q : Nat) (c : Rat) (hc : 2<c)
 (size : (labels T).length≤N) (ss : List Tree) (q : Nat) (budget : q≤Q) (hp : proper T ss=true) :
 (forestWork ordinary (fun _ _ _=>0) T ss q:Rat)≤geometric c*OrdinaryDispatch.WorkIntegration.forestCoefficient N Q*c^q := by
 rw [forestWork_cast]
 have bound := GenericForest.LocalPolynomial.source_work_monomial_size_capped ordinary (fun _ _ _=>0) T N Q c 0 hc (by decide) size
  (by intro t s r _ _ _ _;simp only [Rat.zero_mul];exact Rat.le_refl) ss q budget hp
 simpa only [OrdinaryDispatch.WorkIntegration.forestCoefficient,Rat.zero_add] using bound

theorem forestWork_actual_query_bound (ordinary : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree)
 (N Q q : Nat) (c D : Rat) (hc : 2<c) (hD : 0≤D) (size : (labels T).length≤N) (budget : q≤Q)
 (hp : proper T ss=true)
 (bill : ∀p r,(p,r)∈frontier ordinary T ss q→(W p.1 p.2 r:Rat)≤D*c^r) :
 (forestWork ordinary W T ss q:Rat)≤(D+geometric c*OrdinaryDispatch.WorkIntegration.forestCoefficient N Q)*c^q := by
 rw [forestWork_cast]
 exact GenericForest.FrontierSize.source_work_bound_on_queries ordinary W T Q c _ D hc Rat.natCast_nonneg hD
  (GenericForest.LocalPolynomial.monomial_local_overhead ordinary T N Q c (Rat.le_of_lt hc) size) ss q budget hp bill
end OrdinaryDispatch.WorkRecursion
