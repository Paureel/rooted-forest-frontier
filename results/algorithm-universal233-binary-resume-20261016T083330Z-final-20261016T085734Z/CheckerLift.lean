import BitAccepted
namespace GenericForest.ScalarBits
open RMAF ForestState RestrictionBridge Universal233 Universal233.WholeSourceWork GenericForest.CheckCorrespondence

def stateVolume (T : Option Tree) (ss : List Tree) (q : Nat) :=targetNodes T+sourceNodes ss+ss.length+q
def checkerWidth (L : Nat) (T : Option Tree) (ss : List Tree) (q : Nat) :=
 L+13+8*labelBits (stateVolume T ss q+1)
def InputLabelBits (L : Nat) (T : Option Tree) (ss : List Tree) : Prop :=
 (∀x∈labels T,labelBits x≤L) ∧ (∀s∈ss,∀x∈leaves s,labelBits x≤L)
def PayloadLabelBits (L : Nat) (F : Forest) :=∀x∈F.flatten,labelBits x≤L

theorem labelled_cap (L W : Nat) (xs : List Nat) (LW : L≤W)
 (cap : ∀x∈xs,labelBits x≤L) : LabelCap W xs := by
 intro x hx
 have bitcap : labelBits x≤W:=Nat.le_trans (cap x hx) LW
 have fit:=Nat.lt_log2_self (n:=x)
 have p:=Nat.pow_le_pow_right (n:=2) (by decide) bitcap
 exact Nat.lt_of_lt_of_le fit p

theorem volume_fit (L : Nat) (T : Option Tree) (ss : List Tree) (q x : Nat)
 (bound : x≤stateVolume T ss q) : x<2^(checkerWidth L T ss q) := by
 let M:=stateVolume T ss q
 have p:=pow_mono M 1 8 (by decide)
 simp only [Nat.pow_one] at p
 have xcap : x≤4096*(M+1)^8:=by omega
 have fits:=counter_cap_binary M x xcap
 have width : 13+8*labelBits (M+1)≤checkerWidth L T ss q:=by dsimp [checkerWidth,M];omega
 exact Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (n:=2) (by decide) width)

/-- Closed binary-reference checker theorem, with explicit label width and
semantic payload-size assumptions. No desired scalar cost field is supplied. -/
theorem binary_checked_inspection_bound (L : Nat) (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest)
 (inputs : InputLabelBits L T ss) (payloadLabels : PayloadLabelBits L F) (payload : StatePayloadSize T F) :
 (bitChecked (checkerWidth L T ss q) T ss q F).value=checked T ss q F ∧
 (bitChecked (checkerWidth L T ss q) T ss q F).work≤
 256*(L+14+8*labelBits (stateVolume T ss q+1))*inspectionBill T ss q := by
 let W:=checkerWidth L T ss q
 have positive : 1≤W:=by dsimp [W,checkerWidth];omega
 have LW : L≤W:=by dsimp [W,checkerWidth];omega
 have tc : TargetCap W T:=labelled_cap L W (labels T) LW inputs.1
 have sc : SourcesCap W ss:=fun s hs=>labelled_cap L W (leaves s) LW (inputs.2 s hs)
 have fc : LabelCap W F.flatten:=labelled_cap L W F.flatten LW payloadLabels
 have lab : (labels T).length≤stateVolume T ss q:=by
  have h:=labels_nodes T;dsimp [stateVolume];omega
 have source : (ss.map leaves).flatten.length≤stateVolume T ss q:=by
  have h:=source_leaves_cells ss;dsimp [stateVolume];omega
 have fl : F.length≤stateVolume T ss q:=Nat.le_trans payload.1 lab
 have cells : F.flatten.length≤stateVolume T ss q:=Nat.le_trans payload.2 lab
 have sl : ss.length≤stateVolume T ss q:=by dsimp [stateVolume];omega
 have budget : q≤stateVolume T ss q:=by dsimp [stateVolume];omega
 have r:=bitChecked_refines W T ss q F positive tc sc fc
  (volume_fit L T ss q _ source) (volume_fit L T ss q _ cells)
  (volume_fit L T ss q _ fl) (volume_fit L T ss q _ sl) (volume_fit L T ss q _ budget)
 have old:=checked_work_le_inspection T ss q F payload
 constructor
 · exact r.1.trans (meterChecked_value T ss q F)
 · have h:=Nat.le_trans r.2 (Nat.mul_le_mul_left (beta W) old)
   have factor : beta W=256*(L+14+8*labelBits (stateVolume T ss q+1)):=by
    unfold beta W checkerWidth;congr 1;omega
   rw [factor] at h
   exact h
end GenericForest.ScalarBits
