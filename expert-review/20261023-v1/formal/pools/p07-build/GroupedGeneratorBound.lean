import GroupedEvaluationBound
import BothBadPlanBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState ForestGroups Universal233 WholeSourceWork CoreWork CoreProgram
open GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.GroupedFullQuery Universal233.PaidQueries Universal233.Rule5SelectedLocalWork

theorem generatedOutput_shape (S : Tree) (color : Nat→Nat) (q N : Nat)
 (ns:(leaves S).Nodup) (sn:treeNodes S≤N) (o : Output) (mem:o∈(generate S color q).outputs) :
 o.sourceCuts.length≤N ∧ o.partition.length≤N ∧ ∀U,U∈o.partition→U.length≤N:=by
 have valid:=(Assembly.generated_source_valid S color q o mem).1
 have shape:=RankDichotomy.generate_partition_cost S color q o mem
 have blocks:=SourceCoverage.partitionCheck_block_bound _ _ valid
 have flat:=(FinalCutRecovery.checked_flatten_perm S o.partition ns valid).length_eq
 have sl:=leaves_nodes S
 refine ⟨by omega,by omega,?_⟩
 intro U hu
 have b:=block_cells o.partition U hu
 omega

theorem bothBadOutputsMeter_shape (S : Tree) (A B D : List Nat) (q N : Nat)
 (ns:(leaves S).Nodup) (sn:treeNodes S≤N) (o : Output)
 (mem:o∈(bothBadOutputsMeter S A B D q).value) :
 o.sourceCuts.length≤N ∧ o.partition.length≤N ∧ ∀U,U∈o.partition→U.length≤N:=by
 simp only [bothBadOutputsMeter,appendOutputsMeter_value,List.mem_append,generatedOutputsMeter_value] at mem
 exact mem.elim (generatedOutput_shape S _ q N ns sn o) (generatedOutput_shape S _ q N ns sn o)

def groupedGeneratorCoefficient (N Q : Nat):=2*cheapOutputCoefficient N Q+10

theorem bothBadOutputsMeter_bound (S : Tree) (A B D : List Nat) (q N Q : Nat)
 (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (dl:D.length≤N) (budget:q≤Q) :
 (bothBadOutputsMeter S A B D q).work≤groupedGeneratorCoefficient N Q*2^(q+1) ∧
 (bothBadOutputsMeter S A B D q).value.length≤6*2^(q+1):=by
 have a:=cheapOutputs_uniform S A B D q q N Q sn al bl dl (Nat.le_refl _) budget
 have b:=cheapOutputs_uniform S B A D q q N Q sn bl al dl (Nat.le_refl _) budget
 have pos:1≤2^(q+1):=Nat.two_pow_pos _
 simp only [bothBadOutputsMeter,appendOutputsMeter,List.length_append,groupedGeneratorCoefficient,Nat.add_mul,Nat.mul_assoc]
 exact ⟨by omega,by omega⟩
end OrdinaryDispatch.Hard2SourceWork
