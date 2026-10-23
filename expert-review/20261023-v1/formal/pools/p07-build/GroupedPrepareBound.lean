import GroupedJobsSource
import ForestPretestBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.GroupedFullQuery Universal233.PaidQueries

def groupPrepareOnePolynomial (N : Nat):=forestPretestPolynomial N+2*N+21

theorem groupPrepareOneMeter_bound (p : Problem) (N : Nat)
 (tn:targetNodes p.target≤N) (sn:sourceNodes p.sources≤N) (sl:p.sources.length≤N) :
 (groupPrepareOneMeter p).work≤groupPrepareOnePolynomial N:=by
 have pre:=forestPretestMeter_bound p.target p.sources N tn sn sl
 simp only [groupPrepareOneMeter]
 cases hp:(forestPretestMeter p.target p.sources).value with
 | refused=>simp only [Charged.work,groupPrepareOnePolynomial];omega
 | rejected=>simp only [Charged.work,groupPrepareOnePolynomial];omega
 | found F=>
   have eq:ForestPretest01.pretest01 p.target p.sources=.found F:=by
    simpa only [forestPretestMeter_value] using hp
   have mem:=(ForestPretest01.found_spec p.target p.sources F eq).2.1
   have payload:=pretestCandidate_payload p.sources F mem
   simp only [additionalCostMeter,groupPrepareOnePolynomial];omega

theorem groupPrepareMeter_bound (ps : List Problem) (N : Nat)
 (caps:∀p,p∈ps→targetNodes p.target≤N ∧ sourceNodes p.sources≤N ∧ p.sources.length≤N) :
 (groupPrepareMeter ps).work≤(groupPrepareOnePolynomial N+8)*ps.length+2:=by
 induction ps with
 | nil=>simp [groupPrepareMeter]
 | cons p ps ih=>
   have c:=caps p (by simp)
   have head:=groupPrepareOneMeter_bound p N c.1 c.2.1 c.2.2
   have tail:=ih (by intro x hm;exact caps x (by simp [hm]))
   simp only [groupPrepareMeter,List.length_cons,Nat.mul_add,Nat.mul_one];omega
end OrdinaryDispatch.Hard2SourceWork
