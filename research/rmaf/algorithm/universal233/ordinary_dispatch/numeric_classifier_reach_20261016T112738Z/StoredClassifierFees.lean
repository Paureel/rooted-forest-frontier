import StoredClassifierCaps
namespace OrdinaryDispatch.StoredNumeric.ClassifierReach
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open OrdinaryDispatch.StoredNumeric.ProducerBinding Universal233.WholeSourceWork Universal233.CoreWork

/-- Fully metered classifier fees in node cap N and physical label width B. -/
def restrictionClassifierFee (N B : Nat) :=beta B*(128*(N+1)^2)
theorem restrictionAgreesStored_work (N B : Nat) (T S : GenericForest.BinaryProvider.Tree) (X : Block)
 (tc : TreeWidth B T) (sc : TreeWidth B S) (xc : BlockWidth B X)
 (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N) (xl : X.length≤N) :
 (restrictionAgreesLabels T S X).work≤restrictionClassifierFee N B := by
 have p:=(restrictionAgreesLabels_projects B T S X tc sc xc).2
 have m:=GenericForest.CheckCorrespondence.meterRestrictionAgrees_bound (treeValue T) (treeValue S) (blockValue X) N (by omega) (by omega) (by simpa only [blockValue_length] using xl)
 exact Nat.le_trans p (Nat.mul_le_mul_left _ m)

def badAtFee (N B : Nat) :=8*(N+1)+subtreeSelectorFee N B+restrictionClassifierFee N B+4*B+16

theorem badAtBits_work (N B : Nat) (T S : GenericForest.BinaryProvider.Tree) (e f : RMAF.Vertex)
 (tc : TreeWidth B T) (sc : TreeWidth B S) (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N)
 (ep : e.length≤N) (fp : f.length≤N) : (badAtBits T S e f).work≤badAtFee N B := by
 have eq:=meterAddressEq_bound e f
 have X:=subtreeLeavesBits_work N B S e sc sn ep
 have xc:=subtreeLeavesBits_caps B S e sc
 have xl:=Nat.le_trans xc.2 (Nat.le_trans (bitsLeaves_count S) sn)
 have ag:=restrictionAgreesStored_work N B T S (subtreeLeavesBits S e).value tc sc xc.1 tn sn xl
 have u:=subtreeBits_work S f
 dsimp only [badAtBits]
 split
 · (try dsimp only [Charged.work]);unfold badAtFee;omega
 · split
   · (try dsimp only [Charged.work]);unfold badAtFee;omega
   · cases h : (subtreeBits S f).value with
     | none=>simp only [h];(try dsimp only [Charged.work]);unfold badAtFee;omega
     | some U=>cases U with
       | node l r=>simp only [h];(try dsimp only [Charged.work]);unfold badAtFee;omega
       | leaf c=>
        have cc : c.length≤B:=sc c (subtreeBits_leaf_mem S (.leaf c) f h c (by simp [leavesBits]))
        simp only [h,copyBits_work];(try dsimp only [Charged.work]);unfold badAtFee;omega

theorem badFor_length (T S : GenericForest.BinaryProvider.Tree) (e : RMAF.Vertex) (fs : Addresses) :
 (badFor T S e fs).value.length≤fs.length := by
 induction fs with
 | nil=>simp [badFor]
 | cons f fs ih=>simp only [badFor];split <;> simp only [List.length_cons] <;> omega

theorem badFor_work (N B : Nat) (T S : GenericForest.BinaryProvider.Tree) (e : RMAF.Vertex) (fs : Addresses)
 (tc : TreeWidth B T) (sc : TreeWidth B S) (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N)
 (ep : e.length≤N) (paths : ∀f∈fs,f.length≤N) :
 (badFor T S e fs).work≤(badAtFee N B+6)*(fs.length+1) := by
 induction fs with
 | nil=>simp [badFor,badAtFee]
 | cons f fs ih=>
  have a:=badAtBits_work N B T S e f tc sc tn sn ep (paths f (by simp))
  have r:=ih (fun p hp=>paths p (by simp [hp]))
  simp only [badFor,List.length_cons,Nat.mul_succ] at r ⊢;omega

theorem badCandidatesFrom_work (N B : Nat) (T S : GenericForest.BinaryProvider.Tree) (fs es : Addresses)
 (tc : TreeWidth B T) (sc : TreeWidth B S) (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N)
 (pathsF : ∀f∈fs,f.length≤N) (pathsE : ∀e∈es,e.length≤N) :
 (badCandidatesFrom T S fs es).work≤((badAtFee N B+6)*(fs.length+1)+4*fs.length+9)*(es.length+1) := by
 induction es with
 | nil=>simp [badCandidatesFrom]
 | cons e es ih=>
  have a:=badFor_work N B T S e fs tc sc tn sn (pathsE e (by simp)) pathsF
  have n:=badFor_length T S e fs
  have r:=ih (fun p hp=>pathsE p (by simp [hp]))
  simp only [badCandidatesFrom,appendSpine_work,List.length_cons,Nat.mul_succ] at *;omega

def selectBadFee (N B : Nat) :=pendantSelectorFee N B+((badAtFee N B+6)*(N+1)+4*N+9)*(N+1)+4

theorem selectBadBits_work (N B : Nat) (T S : GenericForest.BinaryProvider.Tree) (a b : Bits)
 (tc : TreeWidth B T) (sc : TreeWidth B S) (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N)
 (ac : a.length≤B) (bc : b.length≤B) : (selectBadBits T S a b).work≤selectBadFee N B := by
 have p:=pendantBits_work N B S a b sc sn ac bc
 have pc:=pendantBits_caps N S a b sn
 have c:=badCandidatesFrom_work N B T S (pendantBits S a b).value (pendantBits S a b).value tc sc tn sn pc.2 pc.2
 have u : (badAtFee N B+6)*((pendantBits S a b).value.length+1)+4*(pendantBits S a b).value.length+9≤(badAtFee N B+6)*(N+1)+4*N+9:=by
  have z:=Nat.mul_le_mul_left (badAtFee N B+6) (Nat.add_le_add_right pc.1 1);omega
 have m:=Nat.mul_le_mul u (Nat.add_le_add_right pc.1 1)
 simp only [selectBadBits,selectBadFee];omega

theorem findClass_work (p : Universal233.CherryBranching.Priority) (cs : List CandidateBits) :
 (findClass p cs).work≤16*(cs.length+1) := by
 induction cs with
 | nil=>simp [findClass]
 | cons c cs ih=>simp only [findClass];split <;> simp only [List.length_cons,Nat.mul_succ] at * <;> omega

theorem selectCandidatesBits_work (cs : List CandidateBits) :
 (selectCandidatesBits cs).work≤48*(cs.length+1)+16 := by
 have a:=findClass_work .common cs;have b:=findClass_work .one cs;have h:=findClass_work .high cs
 dsimp only [selectCandidatesBits]
 split
 · dsimp only [Charged.work];omega
 · split
   · dsimp only [Charged.work];omega
   · split <;> dsimp only [Charged.work] <;> omega

theorem candidatesFrom_work (N B : Nat) (S : GenericForest.BinaryProvider.Tree) (cs : List CherryBits)
 (sc : TreeWidth B S) (sn : treeNodes (treeValue S)≤N) (cap : ∀c∈cs,c.a.length≤B ∧ c.b.length≤B) :
 (candidatesFrom S cs).work≤(pendantSelectorFee N B+8)*(cs.length+1) := by
 induction cs with
 | nil=>simp [candidatesFrom]
 | cons c cs ih=>
  have w:=cap c (by simp)
  have p:=pendantBits_work N B S c.a c.b sc sn w.1 w.2
  have r:=ih (fun x hx=>cap x (by simp [hx]))
  simp only [candidatesFrom,List.length_cons,Nat.mul_succ] at r ⊢;omega

def selectPriorityFee (N B : Nat) :=cherryUnit N B*N+(pendantSelectorFee N B+8)*(N+1)+48*(N+1)+24

theorem selectPriorityBits_work (N B : Nat) (T S : GenericForest.BinaryProvider.Tree)
 (tc : TreeWidth B T) (sc : TreeWidth B S) (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N) :
 (selectPriorityBits T S).work≤selectPriorityFee N B := by
 have c:=cherriesBits_work N B T tc tn
 have cn:=Nat.le_trans (cherriesBits_length T) tn
 have a:=candidatesFrom_work N B S (cherriesBits T).value sc sn (by
  intro x hx;have p:=cherriesBits_provenance T x hx;exact ⟨tc x.a p.1,tc x.b p.2.1⟩)
 have ap:=Nat.mul_le_mul_left (pendantSelectorFee N B+8) (Nat.add_le_add_right cn 1)
 have b:=selectCandidatesBits_work (candidatesBits T S).value
 have bn : (candidatesBits T S).value.length≤N:=by simpa only [candidatesBits,candidatesFrom_length] using cn
 have bp:=Nat.mul_le_mul_left 48 (Nat.add_le_add_right bn 1)
 have cp:=Nat.mul_le_mul_left (cherryUnit N B) tn
 simp only [selectPriorityBits,candidatesBits,selectPriorityFee] at *;omega
end OrdinaryDispatch.StoredNumeric.ClassifierReach
