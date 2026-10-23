import SetupWork
namespace Universal233.Rule5RemainingLocalWork
open RMAF CoreGraph HardParent CoreWork Rule5PrefixLocalWork Rule5PendantLocalWork
open GenericForest.CheckCorrespondence OrdinaryCommonSplit OrdinaryCommonSplit.Source

def setupBudget (N k n : Nat) :=
 16*(N+1)*(N+1)+2*(4*N*N+partitionCap N+3)+(2*N+1)+
 4*N*N+(5*N+5)*(N+1)+incidentBudget k n+8*N*N+N+2*(6*N+1)+
 4*(4*(N+2)*(2*N))+4*((4*(N+3)+4)*(2*N)+3)+40

theorem setup_work (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (N : Nat)
 (tn : (leaves T).length≤N) (sn : (leaves S).length≤N)
 (xy : X.length+Y.length≤N) (pn : p.length≤N) (two : 2≤N) :
 (setupMeter T S X Y p).work≤setupBudget N X.length (leaves T).length := by
 have sqT:=Nat.mul_le_mul_left 4 (Nat.mul_le_mul tn tn)
 have sqS:=Nat.mul_le_mul_left 4 (Nat.mul_le_mul sn sn)
 have lT:=leaves_work T;have lS:=leaves_work S
 have nT:=nodup_tree_work T;have nS:=nodup_tree_work S
 have ndT:=Nat.mul_le_mul_left 8 (Nat.mul_le_mul (Nat.add_le_add_right tn 1) (Nat.add_le_add_right tn 1))
 have ndS:=Nat.mul_le_mul_left 8 (Nat.mul_le_mul (Nat.add_le_add_right sn 1) (Nat.add_le_add_right sn 1))
 have pT:=partition_tree_work T X Y N tn xy two
 have pS:=partition_tree_work S X Y N sn xy two
 have sub:=subtree_work S p
 have per:=Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 5 (show X.length≤N by omega)) 5) (Nat.add_le_add_right sn 1)
 have inc:=incident_work T X
 have mx:=max_work (leaves T++leaves S)
 have tnodes:=treeNodes_le_twice_leaves T
 have snodes:=treeNodes_le_twice_leaves S
 have restriction (U : Tree) (B : List Nat) (un : (leaves U).length≤N) (bn : B.length≤N) :
  (meterRestrict B U).work≤4*(N+2)*(2*N) := by
   have h:=meterRestrict_bound B U
   have nodes:=treeNodes_le_twice_leaves U
   have scaled:=Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.add_le_add_right bn 2)) (show treeNodes U≤2*N by omega)
   omega
 have marking (U : Tree) (B : List Nat) (y r : Nat) (un : (leaves U).length≤N) (bn : B.length≤N) :
  (markedMeter U B y r).work≤(4*(N+3)+4)*(2*N)+3 := by
   have h:=marked_work U B y r
   have nodes:=treeNodes_le_twice_leaves U
   have scaled:=Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (Nat.add_le_add_right bn 3)) 4) (show treeNodes U≤2*N by omega)
   omega
 have x : X.length≤N:=by omega
 have y : Y.length≤N:=by omega
 have r1:=restriction T X tn x;have r2:=restriction S X sn x
 have r3:=restriction T Y tn y;have r4:=restriction S Y sn y
 have m1:=marking T X (Y.headD 0) (labelMax (leaves T++leaves S)+1) tn x
 have m2:=marking S X (Y.headD 0) (labelMax (leaves T++leaves S)+1) sn x
 have m3:=marking T Y (X.headD 0) (labelMax (leaves T++leaves S)+2) tn y
 have m4:=marking S Y (X.headD 0) (labelMax (leaves T++leaves S)+2) sn y
 have splitbill:=setup_split T S X Y p
 unfold setupEnvelope at splitbill
 unfold setupBudget
 simp only [List.length_append] at mx
 simp only [Nat.mul_assoc] at *
 omega
end Universal233.Rule5RemainingLocalWork
