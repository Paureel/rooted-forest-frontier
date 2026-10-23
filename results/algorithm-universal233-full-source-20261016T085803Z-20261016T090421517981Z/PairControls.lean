import PairExact
namespace OrdinaryDispatch.GoodPairDP.Controls
open RMAF ForestState ForestGroups Universal233

def four : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def goodC : Tree := .node (.node (.leaf 4) (.leaf 5)) (.leaf 6)
def badC : Tree := .node (.node (.leaf 4) (.leaf 6)) (.leaf 5)
def target : Tree := .node four goodC
def source (c : Tree) : Tree := .node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) c
def A : List Nat := [0,2]
def B : List Nat := [1,3]
def C : List Nat := [4,5,6]
def depthAnswer : Ordinary := fun t s r=>match DepthOne.pretest01 t s with
 | .found c=>if DepthOne.cutCost c≤r then some (DepthOne.forest s c) else none
 | _=>none

theorem actual_guards : DepthOne.proper target (source badC)=true ∧
 partitionCheck (leaves (source badC)) [A,B,C]=true ∧
 pairwiseEmbeddings (source badC) [A,B,C]=true ∧
 restrictionAgrees target (source badC) A=true ∧ restrictionAgrees target (source badC) B=true ∧
 restrictionAgrees target (source badC) C=false ∧
 disjointVertices (minimalVertices A target) (minimalVertices C target)=true ∧
 disjointVertices (minimalVertices B target) (minimalVertices C target)=true ∧
 [false]∈minimalVertices A target ∧ [false]∈minimalVertices B target := by decide

theorem whole_pair_minimum_paid :
 (AllGoodDP.run (localTarget (some target) (A++B))
  (owned (OutputState.sourceForest (source badC) [A,B,C]) (A++B))).any
  (fun F=>decide (additionalCost (owned (OutputState.sourceForest (source badC) [A,B,C]) (A++B)) F=1))=true := by cbv

theorem bad_outside_actual_budget :
 ((runPair depthAnswer target (source badC) A B C 4).calls.map Universal233.BothBad.Call.budget)=[1] ∧
 (runPair depthAnswer target (source badC) A B C 4).answer.any
  (fun F=>agreement target (source badC) F && decide (F.length-1=4))=true := by cbv

theorem bad_outside_not_free :
 ((runPair depthAnswer target (source badC) A B C 3).calls.map Universal233.BothBad.Call.budget)=[0] ∧
 (runPair depthAnswer target (source badC) A B C 3).answer=none := by cbv

theorem good_outside_zero :
 ((runPair depthAnswer target (source goodC) A B C 3).calls.map Universal233.BothBad.Call.budget)=[0] ∧
 (runPair depthAnswer target (source goodC) A B C 3).answer.any
  (fun F=>agreement target (source goodC) F && decide (F.length-1=3))=true := by cbv

theorem pair_paid_before_outside :
 (runPair depthAnswer target (source badC) A B C 2).answer=none ∧
 (runPair depthAnswer target (source badC) A B C 2).calls=[] := by cbv
end OrdinaryDispatch.GoodPairDP.Controls
