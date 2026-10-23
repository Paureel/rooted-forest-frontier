/- One-shot explicit polynomial presentation of the independently authored join. -/
import FreshJoinV4
namespace FreshOptimizerJoin20261022
open RMAF Universal233 OrdinaryDispatch
open OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.CompleteSource
open OrdinaryDispatch.GlobalSourceAssembly OrdinaryDispatch.RecoveryLocalWork
open OrdinaryDispatch.OuterSource OrdinaryDispatch.Hard2SourceWork

/-- The helper calls have scalar-only arithmetic closure recorded in SCALARS.json.
    n is the original target leaf count; L is the original label-width bound. -/
def explicitCoefficient (n L : Nat) : Nat :=
 n*((outerJoinedPolynomial n n L +
   (disjointRunPolynomial (2*n+3) + badPairLocalPolynomial (2*n+3) n +
     32*(2^50*((2*n+3)+n+2)^8)))*1024*(n+1)) +
 512*(2*n+1)^2 + 64*(recoveryEnvelope n+32)

theorem explicitCoefficient_eq (n L : Nat) : explicitCoefficient n L = coefficient n L := by
 rfl

theorem complete_optimizer_source_join (T S : Tree) (L : Nat)
 (hp : DepthOne.proper T S = true)
 (labels : ∀ x, x ∈ leaves T ++ leaves S → x < 2^L) :
 ∃ (k : Nat) (F : CommonForest) (o : CoreProgram.Output),
   0 < k ∧ agreement T S o.partition = true ∧
   (∀ G, agreement T S G = true → k ≤ G.length) ∧
   (optimize T S).output = some o ∧ o.partition.length = k ∧
   CutRealization.RealizedOutput S o ∧
   (sourceOptimizeMeter (fun b => completeSourceCounter b T S) T S).value = optimize T S ∧
   ((sourceOptimizeMeter (fun b => completeSourceCounter b T S) T S).work : Rat) ≤
     (explicitCoefficient (leaves T).length L : Rat) * (233/100 : Rat)^(k-1) ∧
   (optimize T S).search.trials = failedTrials 0 (k-1) ++ [(k-1,some F)] ∧
   (optimize T S).recoveries = [(F,some o)] := by
 simpa only [explicitCoefficient_eq] using optimizer_source_join T S L hp labels

#print axioms complete_optimizer_source_join
end FreshOptimizerJoin20261022
