import PolynomialCaps
namespace Universal233.Rule5ClosedSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5SelectedLocalWork
open ClassifierCheckFee PaidLiteralDecisionWork

def sideCap (n M : Nat) :=cutsBudget n+(sideAtBudget M+4)*(2*n+1)+2
def withoutCap (n M : Nat) :=sideCap n M+(16*(M+1)^2+4*(M+1)+5)*(2*n+1)+2
def typeCap (n M : Nat) :=(cutsBudget n+partitionBudget n+4)+(singletonPartitionBudget n+4)+2*(arcPartitionBudget M (2*M+1)+3)+5
def literalPlanCap (n M : Nat) :=sideCap n M+withoutCap n M+3*M+typeCap n M+7+M+2
def guardedPlanCap (n M : Nat) :=literalPlanCap n M+5*(guardBudget M+4)+2
def requestsCap (n M : Nat) :=guardedPlanCap n M+4*(requestBudget M+3)+3
def answersCap (n M : Nat) :=requestsCap n M+4*(currentPrefixBudget (2*M)+4)+3
def bestCap (n M k : Nat) :=answersCap n M+4*(agreementK k+3*k+7)+7

def paidPrefixCap (N : Nat) :=paidSelectedBudget N N (checkCap (2*N)) (literalBudget (2*N))+bestCap N (4*N) (2*N)+2

theorem paid_best_cap (T S : Tree) {N M H k K : Nat} (tn:(leaves T).length≤N) (sn:(leaves S).length≤N)
 (mh:M≤H) (kk:k≤K) : paidBestBudget T S M k≤bestCap N H K := by
 simp only [paidBestBudget,answersPrefixBudget,requestsBudget,guardedPlanBudget,literalPlanBudget,rawPlanBudget,
  withoutABudget,sideEdgesBudget,typeBudget,hardBranchBudget,bBranchBudget,targetBranchBudget,
  bestCap,answersCap,requestsCap,guardedPlanCap,literalPlanCap,typeCap,withoutCap,sideCap,
  sideAtBudget,guardBudget,arcPartitionBudget,arcStepBudget,requestBudget,currentPrefixBudget,
  forestPretestBudget,partitionCap,agreementK,cutsBudget,cutGuardBudget,minimalBudget,partitionBudget,coreBudget,pendantPayloadBudget,blocksBudget,payloadCap,singletonPartitionBudget]
 poly_mono

theorem paid_prefix_cap (T S : Tree) {N : Nat} (tn:(leaves T).length≤N) (sn:(leaves S).length≤N) :
 paidExecutionPrefixBudget T S (checkCap ((leaves T).length+(leaves S).length))
 (literalBudget ((leaves T).length+(leaves S).length))≤paidPrefixCap N := by
 have sum:(leaves T).length+(leaves S).length≤2*N:=by omega
 have p:=paid_selected_budget_mono tn sn (check_cap_mono sum) (literal_budget_mono sum)
 have b:=paid_best_cap T S tn sn (show 2*((leaves T).length+(leaves S).length)≤4*N by omega) sum
 simp only [paidExecutionPrefixBudget,paidPrefixCap];omega

/-- An explicit positive Nat polynomial in the original common leaf bound.
The three arm caps are added, so no arm-dependent maximum is hidden. -/
def prefixCap (N : Nat) :=finalBudget N N (checkCap (2*N))+
 forestArmBudget N N (agreementK N)+commonBudget N N (2*N)+paidPrefixCap N+20

theorem selected_prefix_cap (T S : Tree) {N : Nat} (tn:(leaves T).length≤N) (sn:(leaves S).length≤N)
 (z : FinalSelection) :
 finalBudget (leaves T).length (leaves S).length (checkCap ((leaves T).length+(leaves S).length))+
 selectedPrefixBudget T S (checkCap ((leaves T).length+(leaves S).length))
 (literalBudget ((leaves T).length+(leaves S).length)) z+2≤prefixCap N := by
 have sum:(leaves T).length+(leaves S).length≤2*N:=by omega
 have c:=final_budget_mono tn sn (check_cap_mono sum)
 have f:=forest_arm_budget_mono tn sn (agreement_K_mono tn)
 have p:=paid_prefix_cap T S tn sn
 cases z with
 | «prefix» s=>simp only [selectedPrefixBudget,prefixCap];omega
 | remaining d z=>cases z with
  | first u v=>simp only [selectedPrefixBudget,prefixCap];omega
  | third u v=>simp only [selectedPrefixBudget,prefixCap];omega
  | second u v=>simp only [selectedPrefixBudget,prefixCap];omega
  | one e=>
   have x:(subtreeLabels S d.badArc).length≤2*N:=by
    rw [hpLabels_eq]
    have h:=subtreeLabels_length S d.badArc
    have nodes:=treeNodes_le_twice_leaves S;omega
   have m:=common_budget_cap tn sn x
   simp only [selectedPrefixBudget,prefixCap];omega
end Universal233.Rule5ClosedSource
