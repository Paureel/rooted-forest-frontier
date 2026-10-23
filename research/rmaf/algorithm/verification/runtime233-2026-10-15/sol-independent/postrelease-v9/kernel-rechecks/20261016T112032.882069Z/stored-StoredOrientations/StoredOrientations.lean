import StoredSourceSite
namespace OrdinaryDispatch.StoredNumeric
open RMAF Universal233 Universal233.CoreWork GenericForest.ScalarBits GenericForest.BinaryProvider

/-- The source may orient either tree first without an extra recursion edge. -/
def OrientedStep (T S U V : GenericForest.BinaryProvider.Tree) : Prop := StoredStep T S U V ∨ StoredStep S T U V

inductive OrientedPath (T0 S0 : GenericForest.BinaryProvider.Tree) : Nat→GenericForest.BinaryProvider.Tree→GenericForest.BinaryProvider.Tree→Prop where
 | root : OrientedPath T0 S0 0 T0 S0
 | next {d T S U V} : OrientedPath T0 S0 d T S→OrientedStep T S U V→OrientedPath T0 S0 (d+1) U V

theorem oriented_step_caps (B N : Nat) {T S U V : GenericForest.BinaryProvider.Tree}
 (tc : TreeWidth B T) (sc : TreeWidth B S) (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N)
 (step : OrientedStep T S U V) : TreeWidth (B+2) U ∧ TreeWidth (B+2) V ∧
 treeNodes (treeValue U)≤N ∧ treeNodes (treeValue V)≤N := by
 rcases step with forward|reverse
 · exact ⟨(step_width B tc sc forward).1,(step_width B tc sc forward).2,step_nodes N tn sn forward⟩
 · exact ⟨(step_width B sc tc reverse).1,(step_width B sc tc reverse).2,step_nodes N sn tn reverse⟩

theorem oriented_path_caps (B N : Nat) (T0 S0 : GenericForest.BinaryProvider.Tree)
 (tc0 : TreeWidth B T0) (sc0 : TreeWidth B S0) (tn0 : treeNodes (treeValue T0)≤N) (sn0 : treeNodes (treeValue S0)≤N)
 {d T S} (path : OrientedPath T0 S0 d T S) :
 TreeWidth (B+2*d) T ∧ TreeWidth (B+2*d) S ∧ treeNodes (treeValue T)≤N ∧ treeNodes (treeValue S)≤N := by
 induction path with
 | root=>simpa using And.intro tc0 (And.intro sc0 (And.intro tn0 sn0))
 | @next d T S U V path step ih=>
  have caps:=oriented_step_caps (B+2*d) N ih.1 ih.2.1 ih.2.2.1 ih.2.2.2 step
  exact ⟨by simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using caps.1,
   by simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using caps.2.1,caps.2.2⟩

/-- Final label-storage interface. No producer-trace/depth embedding is hidden
in this statement; its depth hypothesis must be discharged at composition. -/
theorem all_orientations_global_caps (B N Q : Nat) (T0 S0 : GenericForest.BinaryProvider.Tree)
 (proper0 : DepthOne.proper (treeValue T0) (treeValue S0)=true)
 (size0 : (leaves (treeValue T0)).length≤N) (tc0 : TreeWidth B T0) (sc0 : TreeWidth B S0)
 {d T S} (path : OrientedPath T0 S0 d T S) (depth : d≤Q+N) :
 TreeWidth (stateStorageWidth B N Q) T ∧ TreeWidth (stateStorageWidth B N Q) S ∧
 treeNodes (treeValue T)≤2*N ∧ treeNodes (treeValue S)≤2*N ∧
 (freshPair T S).value.1.length≤markerStorageWidth B N Q ∧
 (freshPair T S).value.2.length≤markerStorageWidth B N Q := by
 have perm:=((DepthOne.proper_iff _ _).1 proper0).2.2.length_eq
 have tn:=treeNodes_le_twice_leaves (treeValue T0)
 have sn:=treeNodes_le_twice_leaves (treeValue S0)
 have cap:=oriented_path_caps B (2*N) T0 S0 tc0 sc0 (by omega) (by omega) path
 have tw : TreeWidth (stateStorageWidth B N Q) T:=treeWidth_mono cap.1 (by unfold stateStorageWidth;omega)
 have sw : TreeWidth (stateStorageWidth B N Q) S:=treeWidth_mono cap.2.1 (by unfold stateStorageWidth;omega)
 have markers:=freshPair_width (stateStorageWidth B N Q) T S tw sw
 exact ⟨tw,sw,cap.2.2.1,cap.2.2.2,by unfold markerStorageWidth;omega,markers.2⟩
end OrdinaryDispatch.StoredNumeric
