import GroupedGeneratorBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState ForestGroups Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open OrdinaryDispatch.FullSourceWork
open Universal233.GroupedFullQuery Universal233.PaidQueries Universal233.Rule5SelectedLocalWork

def groupedBestCoefficient (N : Nat):=agreementK N+6*N+28

theorem groupedAcceptedMeter_bound (T S : Tree) (q N : Nat) (F : List (List Nat))
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (len:F.length≤2*N) (cells:F.flatten.length≤4*N) :
 (groupedAcceptedMeter T S q F).work≤agreementK N+2*N+8:=by
 have check:=measuredAgreement_K T S N (by omega) (by omega) F (by
  simp only [Rule5LocalWork.cells];omega)
 change (agreementMeter T S F).work≤agreementK N at check
 simp only [groupedAcceptedMeter];omega

def groupedPairCoefficient (N Q : Nat):=
 56*(N+1)^3+groupedGeneratorCoefficient N Q+6*groupedEvaluationCoefficient N+6*groupedBestCoefficient N+24

theorem groupPairLocalSource_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q N Q : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (cl:C.length≤N)
 (ns:(leaves S).Nodup) (address:edge.2.length≤N) (budget:q≤Q) :
 (groupPairLocalSource actual T S A B C edge q).work≤groupedPairCoefficient N Q*2^(q+1) ∧
 (groupPairLocalSource actual T S A B C edge q).value.queries.length≤12*2^(q+1):=by
 let d:=pairDescendantsMeter T edge.2
 let os:=bothBadOutputsMeter S A B d.value q
 let e:=groupEvaluateLocalSource actual T S A B C q os.value
 have dl:d.value.length≤N:=by
  rw [pairDescendantsMeter_value]
  exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_trans (leaves_nodes T) tn)
 have desc:=pairDescendantsMeter_bound T edge.2 N tn address
 have gen:=bothBadOutputsMeter_bound S A B d.value q N Q sn al bl dl budget
 have exec:=groupEvaluateLocalSource_bound actual T S A B C q os.value N tn sn al bl cl
  (by intro o hm;exact bothBadOutputsMeter_shape S A B d.value q N ns sn o hm)
 have check:∀F,F∈e.value.candidates→(groupedAcceptedMeter T S q F).work≤agreementK N+2*N+8:=by
  intro F hm
  have payload:=exec.2.2.2 F hm
  exact groupedAcceptedMeter_bound T S q N F tn sn payload.1 payload.2
 have score:∀F,F∈e.value.candidates→(forestLengthMeter F).work≤2*N+4:=by
  intro F hm;have payload:=exec.2.2.2 F hm
  simp only [forestLengthMeter];omega
 have best:=sourceBestMeter_bound forestLengthMeter (groupedAcceptedMeter T S q) e.value.candidates
  (2*N+4) (agreementK N+2*N+8) score check
 have bestc:(sourceBestMeter forestLengthMeter (groupedAcceptedMeter T S q) e.value.candidates).work≤
  groupedBestCoefficient N*e.value.candidates.length+2:=by
  have eq:agreementK N+2*N+8+2*(2*N+4)+12=groupedBestCoefficient N:=by unfold groupedBestCoefficient;omega
  rw [eq] at best
  exact best
 have pos:1≤2^(q+1):=Nat.two_pow_pos _
 have evcount:e.value.candidates.length≤6*2^(q+1):=Nat.le_trans exec.2.1 gen.2
 have evwork:=Nat.le_trans exec.1 (Nat.add_le_add_right (Nat.mul_le_mul_left (groupedEvaluationCoefficient N) gen.2) 2)
 have bework:=Nat.le_trans bestc (Nat.add_le_add_right (Nat.mul_le_mul_left (groupedBestCoefficient N) evcount) 2)
 have evwork':e.work≤(6*groupedEvaluationCoefficient N)*2^(q+1)+2:=by
  simpa only [←Nat.mul_assoc,Nat.mul_comm (groupedEvaluationCoefficient N) 6] using evwork
 have bework':(sourceBestMeter forestLengthMeter (groupedAcceptedMeter T S q) e.value.candidates).work≤
   (6*groupedBestCoefficient N)*2^(q+1)+2:=by
  simpa only [←Nat.mul_assoc,Nat.mul_comm (groupedBestCoefficient N) 6] using bework
 have desclift:=Nat.mul_le_mul_left (56*(N+1)^3) pos
 have trace:=Nat.le_trans exec.2.2.1 (Nat.mul_le_mul_left 2 gen.2)
 have dd:d.work≤56*(N+1)^3:=desc
 have gg:os.work≤groupedGeneratorCoefficient N Q*2^(q+1):=gen.1
 change e.work≤_ at evwork
 change e.value.queries.length≤_ at trace
 simp only [groupPairLocalSource]
 change d.work+os.work+e.work+(sourceBestMeter forestLengthMeter (groupedAcceptedMeter T S q) e.value.candidates).work+20≤_ ∧ e.value.queries.length≤_
 constructor
 · unfold groupedPairCoefficient
   simp only [Nat.add_mul]
   simp only [Nat.mul_one] at desclift
   omega
 · omega
end OrdinaryDispatch.Hard2SourceWork
