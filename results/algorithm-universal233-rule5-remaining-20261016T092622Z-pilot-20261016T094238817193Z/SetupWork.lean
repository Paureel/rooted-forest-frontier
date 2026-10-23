import SetupBuilder
namespace Universal233.Rule5RemainingLocalWork
open RMAF CoreGraph HardParent CoreWork Rule5PrefixLocalWork Rule5PendantLocalWork
open GenericForest.CheckCorrespondence OrdinaryCommonSplit OrdinaryCommonSplit.Source

/-- All-suffix upper envelope. Successful and refused paths retain their
literal guard costs; only skipped suffixes are overcharged here. -/
def setupEnvelope (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) : Nat :=
 (nodupTreeMeter T).work+(nodupTreeMeter S).work+
 (partitionTreeMeter T X Y).work+(partitionTreeMeter S X Y).work+
 (subtreeMeter S p).work+
 4*(leaves S).length*(leaves S).length+(5*X.length+5)*((leaves S).length+1)+
 (incidentMeter T X).work+
 (leavesMeter T).work+(leavesMeter S).work+(leaves T).length+
 2*(maxMeter (leaves T++leaves S)).work+
 (meterRestrict X T).work+(meterRestrict X S).work+
 (meterRestrict Y T).work+(meterRestrict Y S).work+
 (markedMeter T X (Y.headD 0) (labelMax (leaves T++leaves S)+1)).work+
 (markedMeter S X (Y.headD 0) (labelMax (leaves T++leaves S)+1)).work+
 (markedMeter T Y (X.headD 0) (labelMax (leaves T++leaves S)+2)).work+
 (markedMeter S Y (X.headD 0) (labelMax (leaves T++leaves S)+2)).work+40

theorem setup_split (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) :
 (setupMeter T S X Y p).work≤setupEnvelope T S X Y p := by
 have ucap (U : Tree) (hu : subtree S p=some U) :
  (leavesMeter U).work+(permMeter (leaves U) X).work≤
  4*(leaves S).length*(leaves S).length+(5*X.length+5)*((leaves S).length+1) := by
   have len:=(DepthOne.subtree_leaves_sublist S U p hu).length_le
   have l:=leaves_work U;have r:=perm_work (leaves U) X
   have sq:=Nat.mul_le_mul_left 4 (Nat.mul_le_mul len len)
   have cap:=Nat.mul_le_mul_left (5*X.length+5) (Nat.add_le_add_right len 1)
   simp only [Nat.mul_assoc] at l sq ⊢;omega
 unfold setupEnvelope
 simp only [setupMeter,bump_work]
 split
 · simp only [bump_work]
   split
   · simp only [bump_work]
     split
     · simp only [bump_work]
       split
       · simp only [bump_work]
         split
         · simp only [bump_work]
           split
           · dsimp only;omega
           · rename_i U hu
             have caps:=ucap U hu
             simp only [bump_work]
             split
             · simp only [bump_work]
               split
               · simp only [bump_work]
                 split <;> dsimp only <;> omega
               · dsimp only;omega
             · dsimp only;omega
         · dsimp only;omega
       · dsimp only;omega
     · dsimp only;omega
   · dsimp only;omega
 · dsimp only;omega
end Universal233.Rule5RemainingLocalWork
