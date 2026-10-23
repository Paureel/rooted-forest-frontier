import NewSourceOptimizer
namespace ExplicitSourceOptimizer20261022
open RMAF Universal233 OrdinaryDispatch
open OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.CompleteSource
open OrdinaryDispatch.GlobalSourceAssembly OrdinaryDispatch.RecoveryLocalWork
open OrdinaryDispatch.OuterSource OrdinaryDispatch.Hard2SourceWork

/-- Fixed input-only arithmetic coefficient. Every named term on the right is
an existing canonical polynomial definition, never a work/callback oracle. -/
def sourceOptimizerPolynomial (n L : Nat) : Nat :=
  n*((outerJoinedPolynomial n n L+
    (disjointRunPolynomial (2*n+3)+badPairLocalPolynomialExpression (2*n+3) n+
      32*(2^50*(2*n+3+n+2)^8)))*1024*(n+1))+
  512*(2*n+1)^2+64*(recoveryEnvelope n+32)

theorem coefficient_exact (n L : Nat) :
    sourceOptimizerPolynomial n L=completeOptimizeCoefficient n L := by
  unfold sourceOptimizerPolynomial completeOptimizeCoefficient completeQueryPolynomial recoverySourceEnvelope
  rw [completeSourcePolynomial_explicit]

/-- The literal source meter of the newly proved original optimizer is bounded
by an explicit fixed polynomial times (233/100)^(k-1), with k globally optimum. -/
theorem optimum_k_source_bound (T S : Tree) (L : Nat)
    (proper : DepthOne.proper T S=true)
    (labels : ∀x,x∈leaves T++leaves S → x<2^L) :
    ∃ k o,
      (optimize T S).output=some o ∧
      o.partition.length=k ∧ 0<k ∧
      agreement T S o.partition=true ∧
      (∀G,agreement T S G=true → k≤G.length) ∧
      (sourceOptimizeMeter (fun b=>completeSourceCounter b T S) T S).value=optimize T S ∧
      ((sourceOptimizeMeter (fun b=>completeSourceCounter b T S) T S).work : Rat)≤
        (sourceOptimizerPolynomial (leaves T).length L : Rat)*(233/100:Rat)^(k-1) := by
  obtain ⟨q,F,o,value,selected,trials,out,recoveries,parts,minimum,cost⟩ :=
    CompletedSourceOptimizer20261022.optimizer_source_bound T S L proper labels
  obtain ⟨q',F',o',_,_,out',_,_,_,_,agreement',_,_,_,parts',_,_⟩ :=
    CompletedFunctional233.optimization_correct T S proper
  have same : o'=o := Option.some.inj (out'.symm.trans out)
  subst o'
  refine ⟨o.partition.length,o,out,rfl,by omega,agreement',minimum,value,?_⟩
  simpa only [coefficient_exact,completeSourceOptimize] using cost

#print axioms coefficient_exact
#print axioms optimum_k_source_bound
end ExplicitSourceOptimizer20261022
