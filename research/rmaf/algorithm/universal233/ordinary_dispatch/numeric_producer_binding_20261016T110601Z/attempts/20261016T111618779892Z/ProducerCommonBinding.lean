import ProducerCommonSelectors
import StoredOrientations
namespace OrdinaryDispatch.StoredNumeric.ProducerBinding
open RMAF GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open Universal233.WholeSourceWork Universal233.CoreWork

/-- Additional literal fields of the same checked builder; no assumed selector
representation or arbitrary scalar representative equations. -/
theorem buildSetup_representatives (T S : RMAF.Tree) (X Y : List Nat) (p : RMAF.Vertex)
 (d : OrdinaryCommonSplit.Caller.Setup) (h : OrdinaryCommonSplit.Source.buildSetup T S X Y p=some d) :
 d.x=X.headD 0 ∧ d.y=Y.headD 0 := by
 unfold OrdinaryCommonSplit.Source.buildSetup at h
 split at h
 · split at h
   · split at h
     · split at h
       · split at h
         · split at h
           · simp at h
           · split at h
             · split at h
               · dsimp only at h
                 split at h
                 · cases Option.some.inj h;exact ⟨rfl,rfl⟩
                 · simp at h
               · simp at h
             · simp at h
         · simp at h
       · simp at h
     · simp at h
   · simp at h
 · simp at h

structure CommonSelectors where
 X : Block
 Y : Block
 x : Bits
 y : Bits
 deriving Repr

def commonSelectorsBits (S : GenericForest.BinaryProvider.Tree) (a b c : Bits) (badArc : RMAF.Vertex) : Charged CommonSelectors :=
 let X:=subtreeLeavesBits S badArc;let Y:=outsideSelectorBits S a b c
 let x:=headRepresentative X.value;let y:=headRepresentative Y.value
 ⟨⟨X.value,Y.value,x.value,y.value⟩,X.work+Y.work+x.work+y.work+16⟩

@[simp] theorem commonSelectorsBits_value (S : GenericForest.BinaryProvider.Tree) (a b c : Bits) (p : RMAF.Vertex) :
 let s:=(commonSelectorsBits S a b c p).value
 blockValue s.X=Universal233.HardParent.subtreeLabels (treeValue S) p ∧
 blockValue s.Y=Universal233.CherryBranching.coreLabels (treeValue S) (decode a) (decode b)++[decode c] ∧
 decode s.x=(blockValue s.X).headD 0 ∧ decode s.y=(blockValue s.Y).headD 0 := by
 simp only [commonSelectorsBits,subtreeLeavesBits_value,sourceSubtreeLabels_eq,outsideSelectorBits_value,headRepresentative_value,and_self]

theorem commonSelectorsBits_width (B : Nat) (S : GenericForest.BinaryProvider.Tree) (a b c : Bits) (p : RMAF.Vertex)
 (sc : TreeWidth B S) (cc : c.length≤B) :
 let s:=(commonSelectorsBits S a b c p).value
 BlockWidth B s.X ∧ BlockWidth B s.Y ∧ s.x.length≤B ∧ s.y.length≤B := by
 have X:=(subtreeLeavesBits_caps B S p sc).1
 have Y:=outsideSelectorBits_width B S a b c sc cc
 exact ⟨X,Y,headRepresentative_width B _ X,headRepresentative_width B _ Y⟩

def commonSelectedPayload (T S : GenericForest.BinaryProvider.Tree) (a b c : Bits) (p : RMAF.Vertex) : Charged CommonPayload :=
 let s:=commonSelectorsBits S a b c p
 let r:=commonPayloadBits T S s.value.X s.value.Y s.value.x s.value.y
 ⟨r.value,s.work+r.work+8⟩

/-- Named common-source site. The classifier supplies its stored c with a typed
projection; both selector lists and both representatives are built here. -/
theorem commonSelectedPayload_source_site (T S : GenericForest.BinaryProvider.Tree) (a b c : Bits)
 (bad : Universal233.Rule5FinalClassification.BadSelection) (p : RMAF.Vertex) (d : OrdinaryCommonSplit.Caller.Setup)
 (hc : decode c=bad.c)
 (built : OrdinaryCommonSplit.Source.buildSetup (treeValue T) (treeValue S)
  (Universal233.HardParent.subtreeLabels (treeValue S) bad.badArc)
  (Universal233.Rule5CommonSelector.outsideLabels (treeValue S) (decode a) (decode b) bad) p=some d) :
 let out:=(commonSelectedPayload T S a b c bad.badArc).value
 decode out.rho=d.rho ∧ decode out.gamma=d.gamma ∧
 [targetValue out.tx,targetValue out.sx,targetValue out.ty,targetValue out.sy,
  targetValue out.mxT,targetValue out.mxS,targetValue out.myT,targetValue out.myS]=
 [some d.tx,some d.sx,some d.ty,some d.sy,some d.mxT,some d.mxS,some d.myT,some d.myS] := by
 let s:=(commonSelectorsBits S a b c bad.badArc).value
 have v:=commonSelectorsBits_value S a b c bad.badArc
 change blockValue s.X=_ ∧ blockValue s.Y=_ ∧ decode s.x=_ ∧ decode s.y=_ at v
 have Y : blockValue s.Y=Universal233.Rule5CommonSelector.outsideLabels (treeValue S) (decode a) (decode b) bad:=by
  rw [v.2.1,hc];rfl
 have h : OrdinaryCommonSplit.Source.buildSetup (treeValue T) (treeValue S) (blockValue s.X) (blockValue s.Y) p=some d:=by
  rw [v.1,Y];exact built
 have reps:=buildSetup_representatives _ _ _ _ _ d h
 exact commonPayload_source_site T S s.X s.Y s.x s.y p d h (v.2.2.1.trans reps.1.symm) (v.2.2.2.trans reps.2.symm)

theorem subtreeBits_leaf_mem (S U : GenericForest.BinaryProvider.Tree) (p : RMAF.Vertex)
 (h : (subtreeBits S p).value=some U) : ∀x,x∈leavesBits U→x∈leavesBits S := by
 induction p generalizing S with
 | nil=>simp only [subtreeBits,Option.some.injEq] at h;subst U;exact fun _ hx=>hx
 | cons b ps ih=>
  cases S with
  | leaf x=>simp [subtreeBits] at h
  | node l r=>
   cases b
   · intro x hx;exact List.mem_append_left _ (ih l h x hx)
   · intro x hx;exact List.mem_append_right _ (ih r h x hx)

theorem subtreeLeavesBits_mem (S : GenericForest.BinaryProvider.Tree) (p : RMAF.Vertex) :
 ∀x,x∈(subtreeLeavesBits S p).value→x∈leavesBits S := by
 cases h : (subtreeBits S p).value with
 | none=>simp [subtreeLeavesBits,h]
 | some U=>simpa only [subtreeLeavesBits,h,leavesCopy_value] using subtreeBits_leaf_mem S U p h

theorem outsideSelectorBits_mem (S : GenericForest.BinaryProvider.Tree) (a b c : Bits) (cc : c∈leavesBits S) :
 ∀x,x∈(outsideSelectorBits S a b c).value→x∈leavesBits S := by
 intro x hx
 simp only [outsideSelectorBits,appendLabels_value,copyBits_value,List.mem_append,List.mem_singleton] at hx
 rcases hx with hx|rfl
 · exact excludeLabels_mem _ _ x (by simpa only [coreSelectorBits,leavesCopy_value] using hx)
 · exact cc

theorem headRepresentative_mem (X : Block) (ne : X≠[]) : (headRepresentative X).value∈X := by
 cases X with
 | nil=>contradiction
 | cons x xs=>simp [headRepresentative]

/-- Concrete common payload edges enter the old stored-width transport relation.
The source guard supplies selector nonemptiness; c is retained from the actual
source leaves, a local classifier witness still owed by that producer. -/
theorem commonSelectedPayload_stored_step (T S U V : GenericForest.BinaryProvider.Tree) (a b c : Bits) (p : RMAF.Vertex)
 (cc : c∈leavesBits S)
 (nx : (subtreeLeavesBits S p).value≠[]) (ny : (outsideSelectorBits S a b c).value≠[])
 (hu : some U∈payloadTrees (commonSelectedPayload T S a b c p).value)
 (hv : some V∈payloadTrees (commonSelectedPayload T S a b c p).value) : OrientedStep T S U V := by
 left
 apply StoredStep.payload (o:=some U) (p:=some V) (X:=(subtreeLeavesBits S p).value) (Y:=(outsideSelectorBits S a b c).value)
  (x:=(headRepresentative (subtreeLeavesBits S p).value).value) (y:=(headRepresentative (outsideSelectorBits S a b c).value).value)
 · exact List.mem_append_right _ (subtreeLeavesBits_mem S p _ (headRepresentative_mem _ nx))
 · exact List.mem_append_right _ (outsideSelectorBits_mem S a b c cc _ (headRepresentative_mem _ ny))
 · exact hu
 · exact hv
 · rfl
 · rfl
end OrdinaryDispatch.StoredNumeric.ProducerBinding
