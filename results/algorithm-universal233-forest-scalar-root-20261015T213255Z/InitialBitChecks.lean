import ScheduledBitChecks
namespace GenericForest.ScalarBits
open RMAF ForestState RestrictionBridge Universal233 Universal233.WholeSourceWork GenericForest.CheckCorrespondence

theorem binary_proper_inspection_bound (L : Nat) (T : Option Tree) (ss : List Tree) (q : Nat)
 (inputs : InputLabelBits L T ss) :
 (bitProper (checkerWidth L T ss q) T ss).value=proper T ss ∧
 (bitProper (checkerWidth L T ss q) T ss).work≤
 256*(L+14+8*labelBits (stateVolume T ss q+1))*inspectionBill T ss q := by
 let W:=checkerWidth L T ss q
 have positive : 1≤W:=by dsimp [W,checkerWidth];omega
 have LW : L≤W:=by dsimp [W,checkerWidth];omega
 have tc : TargetCap W T:=labelled_cap L W (labels T) LW inputs.1
 have sc : SourcesCap W ss:=fun s hs=>labelled_cap L W (leaves s) LW (inputs.2 s hs)
 have source : (ss.map leaves).flatten.length≤stateVolume T ss q:=by
  have h:=source_leaves_cells ss;dsimp [stateVolume];omega
 have r:=bitProper_refines W T ss positive tc sc (volume_fit L T ss q _ source)
 constructor
 · exact r.1.trans (meterProper_value T ss)
 · have h:=Nat.le_trans r.2 (Nat.mul_le_mul_left (beta W) (proper_work_le_inspection T ss q))
   have factor : beta W=256*(L+14+8*labelBits (stateVolume T ss q+1)):=by
    unfold beta W checkerWidth;congr 1;omega
   rw [factor] at h;exact h

theorem initial_binary_agrees_bound (L : Nat) (T : Option Tree) (ss : List Tree) (q : Nat)
 (proper : ForestState.proper T ss=true) (bits : ∀x∈labels T,labelBits x≤L) :
 (bitAgrees (checkerWidth L T ss q) T ss (ss.map leaves)).value=agrees T ss (ss.map leaves) ∧
 (bitAgrees (checkerWidth L T ss q) T ss (ss.map leaves)).work≤
 256*(L+14+8*labelBits (stateVolume T ss q+1))*inspectionBill T ss q := by
 have h:=binary_accepted_inspection_bound L T ss q (ss.map leaves)
  (proper_input_bits L T ss proper bits)
  (payload_bits_partition L T _ bits (proper_parts _ _ proper).2)
  (state_payload_source T ss proper)
 have sVolume : ss.length≤stateVolume T ss q:=by dsimp [stateVolume];omega
 have sFits:=volume_fit L T ss q ss.length sVolume
 have fFits : (ss.map leaves).length<2^(checkerWidth L T ss q):=by simpa using sFits
 have qFits:=volume_fit L T ss q q (by dsimp [stateVolume];omega)
 have fv:=lengthBits_value (checkerWidth L T ss q) (ss.map leaves) fFits
 have sv:=lengthBits_value (checkerWidth L T ss q) ss sFits
 constructor
 · have v:=h.1
   simp only [bitAccepted,leBits_value,subtractBits_value,fv,sv,encode_value _ q qFits,
    List.length_map,Nat.sub_self,Nat.zero_le,decide_true,Bool.and_true,accepted,additionalCost] at v
   simpa only [List.length_map,Nat.sub_self,Nat.zero_le,decide_true,Bool.and_true] using v
 · have cost:=h.2;simp only [bitAccepted] at cost;omega
end GenericForest.ScalarBits
