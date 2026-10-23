import StoredContract
namespace OrdinaryDispatch.StoredNumeric
open RMAF Universal233.WholeSourceWork Universal233.CoreWork
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.CheckCorrespondence

theorem blockWidth_mono {B W : Nat} {X : Block} (cap : BlockWidth B X) (h : B≤W) : BlockWidth W X :=
 fun x hx=>Nat.le_trans (cap x hx) h

def OptionWidth (B : Nat) (o : Option GenericForest.BinaryProvider.Tree) : Prop :=
 ∀T,o=some T→TreeWidth B T

structure CommonPayload where
 rho : Bits
 gamma : Bits
 tx : Option GenericForest.BinaryProvider.Tree
 sx : Option GenericForest.BinaryProvider.Tree
 ty : Option GenericForest.BinaryProvider.Tree
 sy : Option GenericForest.BinaryProvider.Tree
 mxT : Option GenericForest.BinaryProvider.Tree
 mxS : Option GenericForest.BinaryProvider.Tree
 myT : Option GenericForest.BinaryProvider.Tree
 myS : Option GenericForest.BinaryProvider.Tree
 deriving Repr

/-- Constructor stage after the actual source guards have chosen X,Y,x,y.
Guard/classifier implementations and full Setup assembly are separately owned. -/
def commonPayloadBits (T S : GenericForest.BinaryProvider.Tree) (X Y : Block) (x y : Bits) : Charged CommonPayload :=
 let markers:=freshPair T S
 let tx:=restrictLabels X T;let sx:=restrictLabels X S
 let ty:=restrictLabels Y T;let sy:=restrictLabels Y S
 let mxT:=markedBits T X y markers.value.1;let mxS:=markedBits S X y markers.value.1
 let myT:=markedBits T Y x markers.value.2;let myS:=markedBits S Y x markers.value.2
 ⟨⟨markers.value.1,markers.value.2,tx.value,sx.value,ty.value,sy.value,mxT.value,mxS.value,myT.value,myS.value⟩,
 markers.work+tx.work+sx.work+ty.work+sy.work+mxT.work+mxS.work+myT.work+myS.work+40⟩

@[simp] theorem commonPayloadBits_value (T S : GenericForest.BinaryProvider.Tree) (X Y : Block) (x y : Bits) :
 targetValue (commonPayloadBits T S X Y x y).value.tx=restrict (blockValue X) (treeValue T) ∧
 targetValue (commonPayloadBits T S X Y x y).value.sx=restrict (blockValue X) (treeValue S) ∧
 targetValue (commonPayloadBits T S X Y x y).value.ty=restrict (blockValue Y) (treeValue T) ∧
 targetValue (commonPayloadBits T S X Y x y).value.sy=restrict (blockValue Y) (treeValue S) ∧
 targetValue (commonPayloadBits T S X Y x y).value.mxT=OrdinaryCommonSplit.marked (treeValue T) (blockValue X) (decode y) (decode (freshPair T S).value.1) ∧
 targetValue (commonPayloadBits T S X Y x y).value.mxS=OrdinaryCommonSplit.marked (treeValue S) (blockValue X) (decode y) (decode (freshPair T S).value.1) ∧
 targetValue (commonPayloadBits T S X Y x y).value.myT=OrdinaryCommonSplit.marked (treeValue T) (blockValue Y) (decode x) (decode (freshPair T S).value.2) ∧
 targetValue (commonPayloadBits T S X Y x y).value.myS=OrdinaryCommonSplit.marked (treeValue S) (blockValue Y) (decode x) (decode (freshPair T S).value.2) := by
 simp only [commonPayloadBits,GenericForest.BinaryProducer.restrictLabels_value,markedBits_value,and_self]

theorem commonPayloadBits_width (B : Nat) (T S : GenericForest.BinaryProvider.Tree) (X Y : Block) (x y : Bits)
 (tc : TreeWidth B T) (sc : TreeWidth B S) (hx : x.length≤B) (hy : y.length≤B) :
 let out:=(commonPayloadBits T S X Y x y).value
 out.rho.length≤B+2 ∧ out.gamma.length≤B+2 ∧
 ∀o,o∈[out.tx,out.sx,out.ty,out.sy,out.mxT,out.mxS,out.myT,out.myS]→OptionWidth (B+2) o := by
 dsimp only [commonPayloadBits]
 have markers:=freshPair_width B T S tc sc
 have tw : TreeWidth (B+2) T:=treeWidth_mono tc (by omega)
 have sw : TreeWidth (B+2) S:=treeWidth_mono sc (by omega)
 refine ⟨by omega,markers.2,?_⟩
 intro o ho U hu
 simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact restrictedWidth (B+2) X T U tw hu
 · exact restrictedWidth (B+2) X S U sw hu
 · exact restrictedWidth (B+2) Y T U tw hu
 · exact restrictedWidth (B+2) Y S U sw hu
 · exact markedBits_width (B+2) T U X y _ tw (by omega) (by omega) hu
 · exact markedBits_width (B+2) S U X y _ sw (by omega) (by omega) hu
 · exact markedBits_width (B+2) T U Y x _ tw (by omega) markers.2 hu
 · exact markedBits_width (B+2) S U Y x _ sw (by omega) markers.2 hu

theorem restriction_work (N P B : Nat) (T : GenericForest.BinaryProvider.Tree) (X : Block)
 (tn : treeNodes (treeValue T)≤N) (xl : X.length≤P) (tc : TreeWidth B T) (xc : BlockWidth B X) :
 (restrictLabels X T).work≤GenericForest.ScalarBits.beta B*(4*(P+2)*N) := by
 have project:=restrictLabels_projects B X T xc tc
 have raw:=meterRestrict_bound (blockValue X) (treeValue T)
 have capped:=Nat.mul_le_mul (Nat.mul_le_mul_left 4 (show (blockValue X).length+2≤P+2 by rw [blockValue_length];omega)) tn
 exact Nat.le_trans project.2 (Nat.mul_le_mul_left _ (Nat.le_trans raw capped))

def commonPayloadFee (N P B : Nat) : Nat := freshPairFee N B+
 4*(GenericForest.ScalarBits.beta (B+2)*(4*(P+2)*N))+4*markedFee N P (B+2)+40

theorem commonPayloadBits_work (N P B : Nat) (T S : GenericForest.BinaryProvider.Tree) (X Y : Block) (x y : Bits)
 (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N)
 (xl : X.length≤P) (yl : Y.length≤P) (tc : TreeWidth B T) (sc : TreeWidth B S)
 (xc : BlockWidth B X) (yc : BlockWidth B Y) (hx : x.length≤B) (hy : y.length≤B) :
 (commonPayloadBits T S X Y x y).work≤commonPayloadFee N P B := by
 have tw : TreeWidth (B+2) T:=treeWidth_mono tc (by omega)
 have sw : TreeWidth (B+2) S:=treeWidth_mono sc (by omega)
 have xw : BlockWidth (B+2) X:=blockWidth_mono xc (by omega)
 have yw : BlockWidth (B+2) Y:=blockWidth_mono yc (by omega)
 have mf:=freshPair_work N B T S tn sn tc sc
 have markers:=freshPair_width B T S tc sc
 have tx:=restriction_work N P (B+2) T X tn xl tw xw
 have sx:=restriction_work N P (B+2) S X sn xl sw xw
 have ty:=restriction_work N P (B+2) T Y tn yl tw yw
 have sy:=restriction_work N P (B+2) S Y sn yl sw yw
 have mt:=markedBits_work N P (B+2) T X y (freshPair T S).value.1 tn xl tw xw (by omega) (by omega)
 have ms:=markedBits_work N P (B+2) S X y (freshPair T S).value.1 sn xl sw xw (by omega) (by omega)
 have nt:=markedBits_work N P (B+2) T Y x (freshPair T S).value.2 tn yl tw yw (by omega) markers.2
 have ns:=markedBits_work N P (B+2) S Y x (freshPair T S).value.2 sn yl sw yw (by omega) markers.2
 simp only [commonPayloadBits,commonPayloadFee]
 omega
end OrdinaryDispatch.StoredNumeric
