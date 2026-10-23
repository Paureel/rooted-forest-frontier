import CallerCaps
namespace GenericForest.BinaryCaller
open GenericForest.BinaryProvider GenericForest.ScalarBits GenericForest.CheckCorrespondence
open Universal233.WholeSourceWork

theorem checkerCapacity_global_setup (N L Q : Nat) (T : Option BinaryProvider.Tree)
 (ss : List BinaryProvider.Tree) (q : Bits) (F : BinaryProvider.Forest) (c : Caps N L Q T ss q F) :
 (checkerCapacity T ss q F).work≤
 beta L*(8*(N+1)^2)+beta L*(13*(N+1)^2)+8*Q+24*(L*N)+60*N+
 16*(2*N+1)^2+32*(N+1)^2+49 := by
 have an:=targetLeaf_count N L T c.targetWidth c.targetNodes
 have bn:=sourceLeaf_count N L ss c.sourceWidth c.sourceNodes
 have aw:=targetLabelsCopy_width L T c.targetWidth
 have bw:=sourceLeavesCopy_width L ss c.sourceWidth
 have ab:=Nat.le_trans (bitCells_bound L (targetLabelsCopy T).value aw) (Nat.mul_le_mul_left L an)
 have bb:=Nat.le_trans (bitCells_bound L (sourceLeavesCopy ss).value.flatten (flatten_width L _ bw)) (Nat.mul_le_mul_left L bn)
 have fb:=Nat.le_trans (bitCells_bound L F.flatten (flatten_width L F c.forestWidth)) (Nat.mul_le_mul_left L c.forestCells)
 have a:=(targetLabelsCopy_projects L T c.targetWidth).2
 have ac:=Nat.mul_le_mul_left (beta L) (meterLabels_cap (targetValue T) N c.targetNodes)
 have b:=(sourceLeavesCopy_projects L ss c.sourceWidth).2
 have bs:=meterSourceLeaves_bound (sourcesValue ss) N c.sourceNodes
 have bsn:=Nat.mul_le_mul_left (8*(N+1)) c.sourceNodes
 have bcap : (meterSourceLeaves (sourcesValue ss)).work≤13*(N+1)^2:=by
  have count:=c.sourceCount
  simp only [sourcesValue,List.length_map,Nat.pow_two,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at bs bsn ⊢;omega
 have bc:=Nat.mul_le_mul_left (beta L) bcap
 have prep:=prepareCapacity_work_bound (q::(targetLabelsCopy T).value) (F++(sourceLeavesCopy ss).value)
 have cells : (F++(sourceLeavesCopy ss).value).flatten.length≤2*N:=by
  have f:=c.forestCells;simp only [List.flatten_append,List.length_append];omega
 have blocks : (F++(sourceLeavesCopy ss).value).length≤2*N:=by
  have f:=c.forestCount;have s:=c.sourceCount
  simp only [List.length_append,sourceLeavesCopy_value,List.length_map];omega
 have square:=Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right cells 1) 2)
 have qw:=c.budgetWidth
 have pbound : (prepareCapacity (q::(targetLabelsCopy T).value) (F++(sourceLeavesCopy ss).value)).work≤
 8*Q+24*(L*N)+48*N+16*(2*N+1)^2+34:=by
  simp only [List.flatten_cons,List.flatten_append,List.length_append,List.length_cons,Nat.mul_add] at prep
  omega
 have fl:=spineCounter_work F;have sl:=spineCounter_work ss
 have flcap:=Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right c.forestCount 1) 2)
 have slcap:=Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right c.sourceCount 1) 2)
 have flw:=spineCounter_length F;have slw:=spineCounter_length ss
 have fn:=c.forestCount;have sn:=c.sourceCount
 simp only [checkerCapacity,appendSpine_value,appendSpine_work,widenCapacity_work]
 omega

theorem checker_work_global (N L Q : Nat) (T : Option BinaryProvider.Tree) (ss : List BinaryProvider.Tree)
 (q : Bits) (F : BinaryProvider.Forest) (c : Caps N L Q T ss q F) :
 (checkerFromInput T ss q F).work≤
 beta L*(8*(N+1)^2)+beta L*(13*(N+1)^2)+8*Q+24*(L*N)+60*N+
 16*(2*N+1)^2+32*(N+1)^2+49+beta (L+Q+2*N+3)*(908*(N+1)^6)+4 := by
 have p:=checkerFromInput_polynomial T ss q F N c.targetNodes c.sourceNodes c.sourceCount c.forestCount c.forestCells
 have setup:=checkerCapacity_global_setup N L Q T ss q F c
 have w:=checkerCapacity_global_width N L Q T ss q F c
 have fac : beta (checkerCapacity T ss q F).value.length≤beta (L+Q+2*N+3):=by unfold beta;omega
 have mul:=Nat.mul_le_mul_right (908*(N+1)^6) fac
 omega
end GenericForest.BinaryCaller
