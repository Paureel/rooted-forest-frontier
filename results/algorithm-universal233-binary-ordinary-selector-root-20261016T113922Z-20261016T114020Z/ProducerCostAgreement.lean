import ProducerCostPrimitives
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits GenericForest.CheckCorrespondence Universal233.WholeSourceWork Universal233.CoreWork

theorem beta_mono (L W : Nat) (h : L≤W) : beta L≤beta W := by unfold beta;omega

def agreementCost (N L : Nat) := BinaryCaller.setupPolynomial N L 0+beta (L+2*N+3)*(644*(N+1)^5)+12

theorem properPair_cost (N L : Nat) (T S : BinaryProvider.Tree)
 (tc : TreeWidth L T) (sc : TreeWidth L S) (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N) :
 (properPair T S).work≤48*leafCost N L+8 := by
 have tl:=Nat.le_trans (bitsLeaves_count T) tn;have sl:=Nat.le_trans (bitsLeaves_count S) sn
 have a:=leavesCopy_cost N L T tc tn;have b:=leavesCopy_cost N L S sc sn
 have nt:=(nodupLabels_projects L (leavesBits T) tc).2
 have ns:=(nodupLabels_projects L (leavesBits S) sc).2
 have ct:=(containedLabels_projects L (leavesBits T) (leavesBits S) tc sc).2
 have cs:=(containedLabels_projects L (leavesBits S) (leavesBits T) sc tc).2
 have n1:=meterNodup_bound (blockValue (leavesBits T));have n2:=meterNodup_bound (blockValue (leavesBits S))
 have p1:=Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right tl 1) 2)
 have p2:=Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right sl 1) 2)
 simp only [blockValue_length] at n1 n2
 have nn1:=Nat.mul_le_mul_left (beta L) (Nat.le_trans n1 p1)
 have nn2:=Nat.mul_le_mul_left (beta L) (Nat.le_trans n2 p2)
 have c1:=Nat.mul_le_mul_left (beta L) (meterContained_bound (blockValue (leavesBits T)) (blockValue (leavesBits S)) N (by simpa only [blockValue_length] using tl) (by simpa only [blockValue_length] using sl))
 have c2:=Nat.mul_le_mul_left (beta L) (meterContained_bound (blockValue (leavesBits S)) (blockValue (leavesBits T)) N (by simpa only [blockValue_length] using sl) (by simpa only [blockValue_length] using tl))
 simp only [properPair,leavesCopy_value]
 unfold leafCost at *;omega

theorem agreementPair_cost (N L : Nat) (T S : BinaryProvider.Tree) (F : BinaryProvider.Forest)
 (tc : TreeWidth L T) (sc : TreeWidth L S) (fc : ForestWidth L F)
 (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N)
 (fl : F.length≤N) (cells : F.flatten.length≤N) : (agreementPair T S F).work≤agreementCost N L := by
 have pos : 1≤N:=by cases T <;> simp only [treeValue,treeNodes] at tn <;> omega
 have caps : BinaryCaller.Caps N L 0 (some T) [S] [] F:=by
  refine ⟨tn,?_,pos,?_,?_,by simp [decode],by simp,fc,fl,cells⟩
  · simpa [sourceNodes,sourcesValue] using sn
  · intro t ht
    have e : T=t:=by simpa using ht
    rw [←e];exact tc
  · intro s hs
    have e : s=S:=by simpa using hs
    rw [e];exact sc
 let C:=(checkerCapacity (some T) [S] [] F).value
 have ready:=checkerCapacity_ready (some T) [S] [] F
 have cw:=BinaryCaller.checkerCapacity_global_width N L 0 (some T) [S] [] F caps
 have setup:=BinaryCaller.caller_setup_bound N L 0 (some T) [S] [] F caps
 have tw : TreeWidth C.length T:=ready.target T (by simp)
 have sw : TreeWidth C.length S:=ready.sources S (by simp)
 have a:=(leavesCopy_projects T C.length tw).2
 have b:=(leavesCopy_projects S C.length sw).2
 have p:=(partitionLabels_projects C.length C (leavesBits T) F ready.width ready.positive tw ready.forest ready.forestCells).2
 have q:=(partitionLabels_projects C.length C (leavesBits S) F ready.width ready.positive sw ready.forest ready.forestCells).2
 have r:=(allChecks_projects C.length blockValue (restrictionAgreesLabels T S)
   (meterRestrictionAgrees (treeValue T) (treeValue S)) F
   (fun B h=>restrictionAgreesLabels_projects C.length T S B tw sw (ready.forest B h))).2
 have e:=(pairwiseLabels_projects C.length T F tw ready.forest).2
 have f:=(pairwiseLabels_projects C.length S F sw ready.forest).2
 have tlen:=Nat.le_trans (leaves_nodes (treeValue T)) tn
 have slen:=Nat.le_trans (leaves_nodes (treeValue S)) sn
 have m1:=cap_lift N 8 2 5 _ (meterLeaves_cap _ N tn) (by decide)
 have m2:=cap_lift N 8 2 5 _ (meterLeaves_cap _ N sn) (by decide)
 have m3:=cap_lift N 128 2 5 _ (meterPartition_bound (RMAF.leaves (treeValue T)) (forestValue F) N tlen (by simpa using fl) (by simpa [forestValue_flatten] using cells)) (by decide)
 have m4:=cap_lift N 128 2 5 _ (meterPartition_bound (RMAF.leaves (treeValue S)) (forestValue F) N slen (by simpa using fl) (by simpa [forestValue_flatten] using cells)) (by decide)
 have m5:=cap_lift N 132 3 5 _ (cap_all (meterRestrictionAgrees (treeValue T) (treeValue S)) (forestValue F) N 128 2
  (by simpa using fl) (fun B h=>meterRestrictionAgrees_bound _ _ B N (by omega) (by omega)
   (Nat.le_trans (block_cells _ B h) (by simpa [forestValue_flatten] using cells)))) (by decide)
 have m6:=meterPairwise_polynomial (treeValue T) (forestValue F) N tn tlen (by simpa using fl)
  (fun B h=>Nat.le_trans (block_cells _ B h) (by simpa [forestValue_flatten] using cells))
 have m7:=meterPairwise_polynomial (treeValue S) (forestValue F) N sn slen (by simpa using fl)
  (fun B h=>Nat.le_trans (block_cells _ B h) (by simpa [forestValue_flatten] using cells))
 have scale (x y k : Nat) (h : x≤beta C.length*y) (m : y≤k*(N+1)^5) : x≤k*(beta C.length*(N+1)^5):=by
  have v:=Nat.le_trans h (Nat.mul_le_mul_left (beta C.length) m)
  simpa only [Nat.mul_left_comm (beta C.length) k ((N+1)^5)] using v
 have z1:=scale _ _ 8 a m1
 have z2:=scale _ _ 8 b m2
 simp only [leaves_projection] at p q
 have z3:=scale _ _ 128 p m3
 have z4:=scale _ _ 128 q m4
 have z5:=scale _ _ 132 r m5
 have z6:=scale _ _ 120 e m6
 have z7:=scale _ _ 120 f m7
 have total : (agreementPair T S F).work≤(checkerCapacity (some T) [S] [] F).work+644*(beta C.length*(N+1)^5)+12:=by
  simp only [C] at z1 z2 z3 z4 z5 z6 z7 ⊢
  simp only [agreementPair,leavesCopy_value]
  omega
 have bm:=Nat.mul_le_mul_right (644*(N+1)^5) (beta_mono C.length (L+2*N+3) (by simpa only [Nat.add_zero] using cw))
 unfold agreementCost
 have eq : beta C.length*(644*(N+1)^5)=644*(beta C.length*(N+1)^5):=Nat.mul_left_comm _ _ _
 rw [eq] at bm;omega
end GenericForest.BinaryProducer
