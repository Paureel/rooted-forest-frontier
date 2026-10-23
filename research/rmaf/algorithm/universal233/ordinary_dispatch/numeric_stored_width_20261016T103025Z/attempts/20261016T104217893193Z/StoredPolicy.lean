import StoredTransport
namespace OrdinaryDispatch.StoredNumeric
open RMAF Universal233 Universal233.CoreWork GenericForest.ScalarBits GenericForest.BinaryProvider

def payloadTrees (p : CommonPayload) : List (Option GenericForest.BinaryProvider.Tree) :=
 [p.tx,p.sx,p.ty,p.sy,p.mxT,p.mxS,p.myT,p.myS]

/-- Constructed producer edges only. Missing recursive-output and overlap
producer bindings are deliberately absent from this transport relation. -/
inductive StoredStep : GenericForest.BinaryProvider.Tree→GenericForest.BinaryProvider.Tree→
 GenericForest.BinaryProvider.Tree→GenericForest.BinaryProvider.Tree→Prop where
 | retained {T S U V} : RetainedTree [T,S] U→RetainedTree [T,S] V→StoredStep T S U V
 | common {T S a b} : a∈leavesBits T++leavesBits S→b∈leavesBits T++leavesBits S→
   StoredStep T S (contractPairBits a b T S).value.1 (contractPairBits a b T S).value.2
 | payload {T S X Y x y o p U V} : x∈leavesBits T++leavesBits S→y∈leavesBits T++leavesBits S→
   o∈payloadTrees (commonPayloadBits T S X Y x y).value→
   p∈payloadTrees (commonPayloadBits T S X Y x y).value→o=some U→p=some V→StoredStep T S U V

theorem step_width (B : Nat) {T S U V : GenericForest.BinaryProvider.Tree}
 (tc : TreeWidth B T) (sc : TreeWidth B S) (step : StoredStep T S U V) : TreeWidth (B+2) U ∧ TreeWidth (B+2) V := by
 have seeds : SourcesWidth B [T,S] := by
  intro A ha;simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl
  · exact tc
  · exact sc
 have leaf (z : Bits) (h : z∈leavesBits T++leavesBits S) : z.length≤B := by
  rcases List.mem_append.1 h with h|h
  · exact tc z h
  · exact sc z h
 cases step with
 | retained a b=>exact ⟨treeWidth_mono (retained_width B _ seeds a) (by omega),treeWidth_mono (retained_width B _ seeds b) (by omega)⟩
 | common a b=>
  have c:=contractPairBits_width B _ _ T S tc sc
  exact ⟨treeWidth_mono c.1 (by omega),treeWidth_mono c.2 (by omega)⟩
 | @payload _ _ X Y x y _ _ _ _ hx hy ho hp eu ev=>
  have widths:=commonPayloadBits_width B T S X Y x y tc sc (leaf _ hx) (leaf _ hy)
  exact ⟨widths.2.2 _ ho _ eu,widths.2.2 _ hp _ ev⟩

theorem step_nodes (N : Nat) {T S U V : GenericForest.BinaryProvider.Tree}
 (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N) (step : StoredStep T S U V) :
 treeNodes (treeValue U)≤N ∧ treeNodes (treeValue V)≤N := by
 have seeds : ∀A,A∈[T,S]→treeNodes (treeValue A)≤N := by
  intro A ha;simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl
  · exact tn
  · exact sn
 cases step with
 | retained a b=>exact ⟨retained_nodes N _ seeds a,retained_nodes N _ seeds b⟩
 | common a b=>exact ⟨Nat.le_trans (contractBits_nodes _ _ _ T) tn,Nat.le_trans (contractBits_nodes _ _ _ S) sn⟩
 | @payload _ _ X Y x y _ _ _ _ hx hy ho hp eu ev=>
  have nodes:=commonPayloadBits_nodes N T S X Y x y tn sn
  exact ⟨nodes _ ho _ eu,nodes _ hp _ ev⟩

inductive StoredPath (T0 S0 : GenericForest.BinaryProvider.Tree) : Nat→GenericForest.BinaryProvider.Tree→GenericForest.BinaryProvider.Tree→Prop where
 | root : StoredPath T0 S0 0 T0 S0
 | next {d T S U V} : StoredPath T0 S0 d T S→StoredStep T S U V→StoredPath T0 S0 (d+1) U V

theorem path_caps (B N : Nat) (T0 S0 : GenericForest.BinaryProvider.Tree)
 (tc0 : TreeWidth B T0) (sc0 : TreeWidth B S0) (tn0 : treeNodes (treeValue T0)≤N) (sn0 : treeNodes (treeValue S0)≤N)
 {d T S} (path : StoredPath T0 S0 d T S) :
 TreeWidth (B+2*d) T ∧ TreeWidth (B+2*d) S ∧ treeNodes (treeValue T)≤N ∧ treeNodes (treeValue S)≤N := by
 induction path with
 | root=>simpa using And.intro tc0 (And.intro sc0 (And.intro tn0 sn0))
 | @next d T S U V path step ih=>
  have width:=step_width (B+2*d) ih.1 ih.2.1 step
  have nodes:=step_nodes N ih.2.2.1 ih.2.2.2 step
  exact ⟨by simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using width.1,
   by simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using width.2,nodes⟩

def stateStorageWidth (B N Q : Nat) : Nat := B+2*(Q+N)
def markerStorageWidth (B N Q : Nat) : Nat := stateStorageWidth B N Q+2

/-- Conditional composition interface. The earlier semantic package proves
d<=Q+N on its exact Reach relation. A complete producer must still prove that
its stored execution embeds both that relation and StoredPath at the same d. -/
theorem global_storage_caps (B N Q : Nat) (T0 S0 : GenericForest.BinaryProvider.Tree)
 (proper0 : DepthOne.proper (treeValue T0) (treeValue S0)=true)
 (size0 : (leaves (treeValue T0)).length≤N) (tc0 : TreeWidth B T0) (sc0 : TreeWidth B S0)
 {d T S} (path : StoredPath T0 S0 d T S) (depth : d≤Q+N) :
 TreeWidth (stateStorageWidth B N Q) T ∧ TreeWidth (stateStorageWidth B N Q) S ∧
 treeNodes (treeValue T)≤2*N ∧ treeNodes (treeValue S)≤2*N ∧
 (freshPair T S).value.1.length≤markerStorageWidth B N Q ∧
 (freshPair T S).value.2.length≤markerStorageWidth B N Q := by
 have perm:=((DepthOne.proper_iff _ _).1 proper0).2.2.length_eq
 have tn:=treeNodes_le_twice_leaves (treeValue T0)
 have sn:=treeNodes_le_twice_leaves (treeValue S0)
 have cap:=path_caps B (2*N) T0 S0 tc0 sc0 (by omega) (by omega) path
 have tw : TreeWidth (stateStorageWidth B N Q) T:=treeWidth_mono cap.1 (by unfold stateStorageWidth;omega)
 have sw : TreeWidth (stateStorageWidth B N Q) S:=treeWidth_mono cap.2.1 (by unfold stateStorageWidth;omega)
 have markers:=freshPair_width (stateStorageWidth B N Q) T S tw sw
 exact ⟨tw,sw,cap.2.2.1,cap.2.2.2,by unfold markerStorageWidth;omega,markers.2⟩

/-- Decoded zero has arbitrarily padded representations. No semantic label cap
L can replace initial stored width B in the preceding transport theorem. -/
theorem padded_zero (n : Nat) : decode (List.replicate n false)=0 := by
 induction n <;> simp_all [List.replicate_succ,decode,bit]
end OrdinaryDispatch.StoredNumeric
