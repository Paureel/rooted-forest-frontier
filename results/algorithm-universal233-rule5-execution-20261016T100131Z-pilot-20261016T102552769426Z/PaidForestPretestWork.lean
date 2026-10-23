import PaidForestCandidateWork
namespace Universal233.Rule5ExecutionSource
open RMAF ForestState CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence

def forestPretestBudget (N : Nat) :=164*(N+1)^3+8192*(N+1)^5+
 (888*(2*N+3)^6+4*N+12)*(N+1)+5

theorem forest_pretest_work (T : Option Tree) (ss : List Tree) (N : Nat)
 (tn : targetNodes T≤N) (sn : sourceNodes ss≤N) :
 (forestPretestMeter T ss).work≤forestPretestBudget N := by
 have sl:=Nat.le_trans (source_count_nodes ss) sn
 have proper:=meterProper_cap T ss N tn sn sl
 have cs:=forest_candidates_work ss N sn
 have count:=forest_candidates_count ss
 have check (F : Forest) (mem : F∈(forestCandidatesMeter ss).value) :
  (meterAgrees T ss F).work≤888*(2*N+3)^6 := by
   have p:=forest_candidates_payload ss mem
   have h:=meterAgrees_cap T ss F (2*N+2) (by omega) (by omega) (by omega) (by omega) (by omega)
   simpa only [Nat.add_assoc,Nat.reduceAdd] using h
 have best:=best_additional_work ss (meterAgrees T ss) (forestCandidatesMeter ss).value
  (888*(2*N+3)^6) (N+1) check (fun F hf=>by have p:=forest_candidates_payload ss hf;omega)
 have coeff : 888*(2*N+3)^6+2*(N+1)+2*ss.length+10≤888*(2*N+3)^6+4*N+12 := by omega
 have scale:=Nat.mul_le_mul coeff (show (forestCandidatesMeter ss).value.length≤N+1 by omega)
 simp only [forestPretestMeter]
 split <;> dsimp only <;> unfold forestPretestBudget <;> omega
end Universal233.Rule5ExecutionSource
