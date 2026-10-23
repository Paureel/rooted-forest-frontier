import ForestPretestConstructionBound
import SourceBestBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork

def forestPretestPolynomial (N : Nat):=
 164*(N+1)^3+pretestConstructionPolynomial N+
 (888*(2*N+3)^6+2*(2*N+5)+12)*(N+1)+18

/-- Literal current-forest pretest: properness, unchanged and every one-cut
candidate, all original checkers, and both score computations in every minimum. -/
theorem forestPretestMeter_bound (T : Option Tree) (ss : List Tree) (N : Nat)
 (tn:targetNodes T≤N) (sn:sourceNodes ss≤N) (sl:ss.length≤N) :
 (forestPretestMeter T ss).work≤forestPretestPolynomial N:=by
 have p:=meterProper_cap T ss N tn sn sl
 have c:=pretestCandidatesMeter_bound ss N sn sl
 have clen:(pretestCandidatesMeter ss).value.length≤N+1:=by
  rw [pretestCandidatesMeter_value]
  simp only [ForestPretest01.candidates,List.length_cons]
  have k:=oneCutsForest_count ss
  omega
 have cost:∀F,F∈(pretestCandidatesMeter ss).value→(additionalCostMeter ss F).work≤2*N+5:=by
  intro F hm
  have m:F∈ForestPretest01.candidates ss:=by simpa only [pretestCandidatesMeter_value] using hm
  have payload:=pretestCandidate_payload ss F m
  simp only [additionalCostMeter];omega
 have check:∀F,F∈(pretestCandidatesMeter ss).value→(meterAgrees T ss F).work≤888*(2*N+3)^6:=by
  intro F hm
  have m:F∈ForestPretest01.candidates ss:=by simpa only [pretestCandidatesMeter_value] using hm
  have payload:=pretestCandidate_payload ss F m
  exact meterAgrees_cap T ss F (2*N+2) (by omega) (by omega) (by omega) (by omega) (by omega)
 have b:=sourceBestMeter_bound (additionalCostMeter ss) (meterAgrees T ss)
  (pretestCandidatesMeter ss).value (2*N+5) (888*(2*N+3)^6) cost check
 have mul:=Nat.mul_le_mul_left (888*(2*N+3)^6+2*(2*N+5)+12) clen
 simp only [forestPretestMeter,forestPretestPolynomial]
 split <;> simp only [Charged.work] <;> omega
end OrdinaryDispatch.Hard2SourceWork
