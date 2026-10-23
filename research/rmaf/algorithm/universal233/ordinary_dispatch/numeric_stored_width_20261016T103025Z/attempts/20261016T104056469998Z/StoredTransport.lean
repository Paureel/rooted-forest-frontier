import StoredCommonPayload
namespace OrdinaryDispatch.StoredNumeric
open RMAF Universal233.WholeSourceWork Universal233.CoreWork
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer GenericForest.CheckCorrespondence

theorem restriction_nodes (T U : GenericForest.BinaryProvider.Tree) (X : Block)
 (h : (restrictLabels X T).value=some U) : treeNodes (treeValue U)≤treeNodes (treeValue T) := by
 have value:=restrictLabels_value X T
 have original : restrict (blockValue X) (treeValue T)=some (treeValue U) := by simpa only [h,targetValue,Option.map_some] using value.symm
 exact restricted_nodes _ _ _ original

theorem markedBits_nodes (T U : GenericForest.BinaryProvider.Tree) (X : Block) (y rho : Bits)
 (h : (markedBits T X y rho).value=some U) : treeNodes (treeValue U)≤treeNodes (treeValue T) := by
 unfold markedBits at h
 cases r : (restrictLabels (y::X) T).value with
 | none=>simp [r] at h
 | some V=>
  simp only [r,Option.some.injEq] at h;subst U
  rw [relabelSwap_nodes]
  exact restriction_nodes T V (y::X) r

theorem sourceForestBits_nodes (N : Nat) (S : GenericForest.BinaryProvider.Tree) (Q : GenericForest.BinaryProvider.Forest)
 (cap : treeNodes (treeValue S)≤N) : ∀U,U∈(sourceForestBits S Q).value→treeNodes (treeValue U)≤N := by
 induction Q with
 | nil=>simp [sourceForestBits]
 | cons B Q ih=>
  cases h : (restrictLabels B S).value with
  | none=>simpa only [sourceForestBits,h] using ih
  | some T=>
   intro U hu
   simp only [sourceForestBits,h,List.mem_cons] at hu
   rcases hu with rfl|hu
   · exact Nat.le_trans (restriction_nodes S T B h) cap
   · exact ih U hu

theorem replaceBits_nodes (N : Nat) (Q : GenericForest.BinaryProvider.Forest) (i : Bits) (ss : List GenericForest.BinaryProvider.Tree)
 (cap : ∀S,S∈ss→treeNodes (treeValue S)≤N) : ∀U,U∈(replaceBits Q i ss).value→treeNodes (treeValue U)≤N := by
 induction ss generalizing i with
 | nil=>simp [replaceBits]
 | cons s ss ih=>
  have sc:=cap s (by simp)
  have tail : ∀S,S∈ss→treeNodes (treeValue S)≤N := fun S h=>cap S (by simp [h])
  simp only [replaceBits]
  split
  · simp only [appendSpine_value]
    intro U hu
    rcases List.mem_append.1 hu with h|h
    · exact sourceForestBits_nodes N s Q sc U h
    · exact tail U h
  · intro U hu
    rcases List.mem_cons.1 hu with rfl|h
    · exact sc
    · exact ih _ tail U h

theorem subtreeBits_nodes (T U : GenericForest.BinaryProvider.Tree) (p : RMAF.Vertex)
 (h : (subtreeBits T p).value=some U) : treeNodes (treeValue U)≤treeNodes (treeValue T) := by
 induction p generalizing T with
 | nil=>simp only [subtreeBits,Option.some.injEq] at h;subst U;exact Nat.le_refl _
 | cons b p ih=>
  cases T with
  | leaf x=>simp [subtreeBits] at h
  | node l r=>cases b <;> have il:=ih l;have ir:=ih r <;> simp only [subtreeBits,Bool.false_eq_true,ite_false,ite_true] at h
              all_goals first | (have n:=il h;simp only [treeValue,treeNodes];omega) | (have n:=ir h;simp only [treeValue,treeNodes];omega)

/-- Exactly the constructed label-preserving producer operations; it excludes
arbitrary callback answers and any as-yet unconstructed overlap generator. -/
inductive RetainedTree (seeds : List GenericForest.BinaryProvider.Tree) : GenericForest.BinaryProvider.Tree→Prop where
 | seed {T} : T∈seeds→RetainedTree seeds T
 | restriction {T U X} : RetainedTree seeds T→(restrictLabels X T).value=some U→RetainedTree seeds U
 | subtree {T U p} : RetainedTree seeds T→(subtreeBits T p).value=some U→RetainedTree seeds U
 | source {T Q U} : RetainedTree seeds T→U∈(sourceForestBits T Q).value→RetainedTree seeds U
 | replacement {ss Q i U} : (∀T,T∈ss→RetainedTree seeds T)→U∈(replaceBits Q i ss).value→RetainedTree seeds U

theorem retained_width (B : Nat) (seeds : List GenericForest.BinaryProvider.Tree)
 (cap : SourcesWidth B seeds) {T} (path : RetainedTree seeds T) : TreeWidth B T := by
 induction path with
 | seed h=>exact cap _ h
 | restriction _ h ih=>exact restrictedWidth B _ _ _ ih h
 | subtree _ h ih=>exact subtreeBits_width B _ _ _ ih h
 | source _ h ih=>exact (sourceForestBits_caps B _ _ ih).1 _ h
 | replacement _ h ih=>exact replaceBits_width B _ _ _ ih _ h

theorem retained_nodes (N : Nat) (seeds : List GenericForest.BinaryProvider.Tree)
 (cap : ∀S,S∈seeds→treeNodes (treeValue S)≤N) {T} (path : RetainedTree seeds T) : treeNodes (treeValue T)≤N := by
 induction path with
 | seed h=>exact cap _ h
 | restriction _ h ih=>exact Nat.le_trans (restriction_nodes _ _ _ h) ih
 | subtree _ h ih=>exact Nat.le_trans (subtreeBits_nodes _ _ _ h) ih
 | source _ h ih=>exact sourceForestBits_nodes N _ _ ih _ h
 | replacement _ h ih=>exact replaceBits_nodes N _ _ _ ih _ h

theorem commonPayloadBits_nodes (N : Nat) (T S : GenericForest.BinaryProvider.Tree) (X Y : Block) (x y : Bits)
 (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N) :
 let out:=(commonPayloadBits T S X Y x y).value
 ∀o,o∈[out.tx,out.sx,out.ty,out.sy,out.mxT,out.mxS,out.myT,out.myS]→
 ∀U,o=some U→treeNodes (treeValue U)≤N := by
 dsimp only [commonPayloadBits]
 intro o ho U hu
 simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact Nat.le_trans (restriction_nodes _ _ _ hu) tn
 · exact Nat.le_trans (restriction_nodes _ _ _ hu) sn
 · exact Nat.le_trans (restriction_nodes _ _ _ hu) tn
 · exact Nat.le_trans (restriction_nodes _ _ _ hu) sn
 · exact Nat.le_trans (markedBits_nodes _ _ _ _ _ hu) tn
 · exact Nat.le_trans (markedBits_nodes _ _ _ _ _ hu) sn
 · exact Nat.le_trans (markedBits_nodes _ _ _ _ _ hu) tn
 · exact Nat.le_trans (markedBits_nodes _ _ _ _ _ hu) sn
end OrdinaryDispatch.StoredNumeric
