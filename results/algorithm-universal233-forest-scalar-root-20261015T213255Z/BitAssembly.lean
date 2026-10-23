import BitFamilyChecks
namespace GenericForest.ScalarBits
open RMAF ForestState RestrictionBridge Universal233 Universal233.WholeSourceWork GenericForest.CheckCorrespondence

def TargetCap (W : Nat) (T : Option Tree) :=LabelCap W (labels T)
def SourcesCap (W : Nat) (ss : List Tree) :=∀s∈ss,TreeCap W s

theorem source_cells_cap (W : Nat) (ss : List Tree) (cap : SourcesCap W ss) : LabelCap W (ss.map leaves).flatten := by
 intro x hx
 obtain ⟨B,hB,hx⟩:=List.mem_flatten.mp hx
 obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hB
 exact cap s hs x hx

def bitProper (W : Nat) (T : Option Tree) (ss : List Tree) : Charged Bool :=
 let a:=pointerLift W (meterLabels T);let b:=bitNodup W a.value
 let c:=pointerLift W (meterSourceLeaves ss);let d:=bitPartition W a.value c.value
 ⟨b.value&&d.value,a.work+b.work+c.work+d.work+4*beta W⟩

theorem bitProper_refines (W : Nat) (T : Option Tree) (ss : List Tree)
 (positive : 1≤W) (tc : TargetCap W T) (sc : SourcesCap W ss)
 (cellsFit : (ss.map leaves).flatten.length<2^W) :
 Refines W (bitProper W T ss) (meterProper T ss) := by
 have b:=bitNodup_refines W (labels T) tc
 have d:=bitPartition_refines W (labels T) (ss.map leaves) positive tc (source_cells_cap W ss sc) cellsFit
 simp only [Refines] at b d ⊢
 simp only [bitProper,meterProper,pointerLift,meterLabels_value,meterSourceLeaves_value]
 constructor
 · rw [b.1,d.1]
 · simp only [Nat.mul_add,Nat.mul_comm (beta W) 4];omega

def bitTargetAgrees (W : Nat) : Option Tree→Tree→List Nat→Charged Bool
 | none,_,_=>⟨false,beta W⟩ | some t,s,B=>bitRestrictionAgrees W t s B

theorem bitTargetAgrees_refines (W : Nat) (T : Option Tree) (s : Tree) (B : List Nat)
 (tc : TargetCap W T) (sc : TreeCap W s) (bc : LabelCap W B) :
 Refines W (bitTargetAgrees W T s B) (meterTargetAgrees T s B) := by
 cases T with
 | none=>simp [Refines,bitTargetAgrees,meterTargetAgrees]
 | some t=>exact bitRestrictionAgrees_refines W t s B tc sc bc

def bitTargetEmbeddings (W : Nat) : Option Tree→Forest→Charged Bool
 | none,F=>pointerLift W ⟨F.isEmpty,1⟩ | some t,F=>bitPairwise W t F

theorem bitTargetEmbeddings_refines (W : Nat) (T : Option Tree) (F : Forest)
 (tc : TargetCap W T) (fc : LabelCap W F.flatten) :
 Refines W (bitTargetEmbeddings W T F) (meterTargetEmbeddings T F) := by
 cases T with
 | none=>exact pointerLift_refines _ _
 | some t=>exact bitPairwise_refines W t F tc (block_cap W F fc)

def bitSourceCheck (W : Nat) (T : Option Tree) (F : Forest) (s : Tree) : Charged Bool :=
 let a:=pointerLift W (meterLeaves s);let G:=bitFamily W a.value F
 let b:=pointerLift W (meterLeaves s);let p:=bitPartition W b.value G.value
 let r:=bitAll W (bitTargetAgrees W T s) G.value
 let e:=bitPairwise W s G.value
 ⟨p.value&&r.value&&e.value,a.work+G.work+b.work+p.work+r.work+e.work+8*beta W⟩

theorem bitSourceCheck_refines (W : Nat) (T : Option Tree) (F : Forest) (s : Tree)
 (positive : 1≤W) (tc : TargetCap W T) (sc : TreeCap W s)
 (fc : LabelCap W F.flatten) (cellsFit : F.flatten.length<2^W) :
 Refines W (bitSourceCheck W T F s) (meterSourceCheck T F s) := by
 have g:=bitFamily_refines W (leaves s) F sc (block_cap W F fc)
 have gc:=family_cap W (leaves s) F fc
 have gl : (family (leaves s) F).flatten.length<2^W:=Nat.lt_of_le_of_lt (family_cells _ _) cellsFit
 have p:=bitPartition_refines W (leaves s) (family (leaves s) F) positive sc gc gl
 have r:=bitAll_refines W (bitTargetAgrees W T s) (meterTargetAgrees T s) (family (leaves s) F)
  (fun B hB=>bitTargetAgrees_refines W T s B tc sc (block_cap W _ gc B hB))
 have e:=bitPairwise_refines W s (family (leaves s) F) sc (block_cap W _ gc)
 simp only [Refines,meterFamily_value] at g p r e ⊢
 simp only [bitSourceCheck,meterSourceCheck,pointerLift,meterLeaves_value,meterFamily_value,g.1]
 constructor
 · rw [p.1,r.1,e.1]
 · simp only [Nat.mul_add,Nat.mul_comm (beta W) 8];omega

def bitSourceContainment (W : Nat) (B : List Nat) (ss : List Tree) : Charged Bool :=
 bitAny W (fun s=>let a:=pointerLift W (meterLeaves s);let c:=bitContained W B a.value
   ⟨c.value,a.work+c.work+2*beta W⟩) ss

theorem bitSourceContainment_refines (W : Nat) (B : List Nat) (ss : List Tree)
 (bc : LabelCap W B) (sc : SourcesCap W ss) :
 Refines W (bitSourceContainment W B ss) (meterSourceContainment B ss) := by
 apply bitAny_refines
 intro s hs
 have c:=bitContained_refines W B (leaves s) bc (sc s hs)
 simp only [Refines] at c ⊢
 simp only [pointerLift,meterLeaves_value]
 refine ⟨c.1,?_⟩
 simp only [Nat.mul_add,Nat.mul_comm (beta W) 2];omega

def bitAgrees (W : Nat) (T : Option Tree) (ss : List Tree) (F : Forest) : Charged Bool :=
 let p:=bitProper W T ss;let a:=pointerLift W (meterLabels T);let f:=bitPartition W a.value F
 let c:=bitAll W (fun B=>bitSourceContainment W B ss) F
 let e:=bitTargetEmbeddings W T F;let s:=bitAll W (bitSourceCheck W T F) ss
 ⟨p.value&&f.value&&c.value&&e.value&&s.value,p.work+a.work+f.work+c.work+e.work+s.work+8*beta W⟩

theorem bitAgrees_refines (W : Nat) (T : Option Tree) (ss : List Tree) (F : Forest)
 (positive : 1≤W) (tc : TargetCap W T) (sc : SourcesCap W ss) (fc : LabelCap W F.flatten)
 (sourceFit : (ss.map leaves).flatten.length<2^W) (cellsFit : F.flatten.length<2^W) :
 Refines W (bitAgrees W T ss F) (meterAgrees T ss F) := by
 have p:=bitProper_refines W T ss positive tc sc sourceFit
 have f:=bitPartition_refines W (labels T) F positive tc fc cellsFit
 have c:=bitAll_refines W (fun B=>bitSourceContainment W B ss) (fun B=>meterSourceContainment B ss) F
  (fun B hB=>bitSourceContainment_refines W B ss (block_cap W F fc B hB) sc)
 have e:=bitTargetEmbeddings_refines W T F tc fc
 have s:=bitAll_refines W (bitSourceCheck W T F) (meterSourceCheck T F) ss
  (fun s hs=>bitSourceCheck_refines W T F s positive tc (sc s hs) fc cellsFit)
 simp only [Refines] at p f c e s ⊢
 simp only [bitAgrees,meterAgrees,pointerLift,meterLabels_value]
 constructor
 · rw [p.1,f.1,c.1,e.1,s.1]
 · simp only [Nat.mul_add,Nat.mul_comm (beta W) 8];omega
end GenericForest.ScalarBits
