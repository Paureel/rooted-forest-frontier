import PairWitness
namespace Universal233.ClusterFreeWitness
open RMAF Universal233.ScaffoldWitness
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def clusterFreeT : Tree := (.node (.node (.node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 4)) (.node (.node (.leaf 3) (.node (.leaf 9) (.node (.leaf 10) (.node (.leaf 11) (.node (.node (.leaf 12) (.leaf 13)) (.leaf 1)))))) (.leaf 5))) (.leaf 6)) (.node (.leaf 7) (.leaf 8)))

/-- Exact descendant-leaf sets at every actual vertex of the binary input. -/
def descendantClusters : Tree → List (List Nat)
 | .leaf x => [[x]]
 | .node l r => leaves (.node l r) :: (descendantClusters l ++ descendantClusters r)

def noProperCommon (t s : Tree) : Bool :=
 (descendantClusters t).all fun b =>
   if 2 ≤ b.length ∧ b.length < (leaves t).length then
     !((descendantClusters s).any (sameMembers b))
   else true

def assignmentsOn (b tags : List Nat) : List (List Nat) :=
 ((List.range 2).map fun tag =>
   ((b.zip tags).filter fun p => p.2 == tag).map Prod.fst).filter fun c => !c.isEmpty

def localAgrees (t s : Tree) (b : List Nat) (parts : List (List Nat)) : Bool :=
 match restrict b t, restrict b s with
 | some u, some v => agreement u v parts
 | _,_ => false

def everyBadParentRejectsOneCut : Bool :=
 paidPartitions.all fun bs =>
   (bs.filter fun b => !restrictionAgrees clusterFreeT originalS b).all fun b =>
     (assignments b.length 2).all fun tags =>
       !(localAgrees clusterFreeT originalS b (assignmentsOn b tags))

theorem properClusterFreeT : (leaves clusterFreeT).Nodup := by decide
theorem sameOriginalLabels : sameMembers (leaves clusterFreeT) (leaves originalS) = true := by decide
theorem noSharedProperCluster : noProperCommon clusterFreeT originalS = true := by decide
theorem oldPairHasSharedCluster : noProperCommon originalT originalS = false := by decide
theorem cleanIdenticalHasSharedCluster :
 noProperCommon (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
                (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) = false := by decide
theorem paidSourceValidUnchanged : paidPartitions.all (agreement originalS originalS) = true := by decide
theorem paidTargetDisjoint : paidPartitions.all (pairwiseEmbeddings clusterFreeT) = true := by decide
theorem exactlyOneBadParent : paidPartitions.all (fun bs =>
 (bs.filter (fun b => !restrictionAgrees clusterFreeT originalS b)).length == 1) = true := by decide
theorem exactBadLocalDepth1Failure : everyBadParentRejectsOneCut = true := by decide
end Universal233.ClusterFreeWitness
