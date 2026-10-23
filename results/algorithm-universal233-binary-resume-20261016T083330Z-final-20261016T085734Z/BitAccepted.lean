import BitAssembly
namespace GenericForest.ScalarBits
open RMAF ForestState RestrictionBridge Universal233 Universal233.WholeSourceWork GenericForest.CheckCorrespondence

def bitAccepted (W : Nat) (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest) : Charged Bool :=
 let a:=bitAgrees W T ss F;let fl:=lengthBits W F;let sl:=lengthBits W ss
 let d:=subtractBits fl.value sl.value;let b:=leBits d.value (encode W q)
 ⟨a.value&&b.value,a.work+fl.work+sl.work+d.work+b.work+4*beta W⟩

theorem bitAccepted_refines (W : Nat) (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest)
 (positive : 1≤W) (tc : TargetCap W T) (sc : SourcesCap W ss) (fc : LabelCap W F.flatten)
 (sourceFit : (ss.map leaves).flatten.length<2^W) (cellsFit : F.flatten.length<2^W)
 (fFit : F.length<2^W) (sFit : ss.length<2^W) (qFit : q<2^W) :
 Refines W (bitAccepted W T ss q F) (meterAccepted T ss q F) := by
 have a:=bitAgrees_refines W T ss F positive tc sc fc sourceFit cellsFit
 have fv:=lengthBits_value W F fFit
 have sv:=lengthBits_value W ss sFit
 have fl:=lengthBits_length W F;have sl:=lengthBits_length W ss
 have dl:=subtractBits_length (lengthBits W F).value (lengthBits W ss).value
 have dw : (subtractBits (lengthBits W F).value (lengthBits W ss).value).value.length≤W:=by omega
 have fw:=lengthBits_work W F positive
 have sw:=lengthBits_work W ss positive
 have d:=(scalar_width_bounds W (lengthBits W F).value (lengthBits W ss).value fl sl).2.2.2
 have b:=(scalar_width_bounds W (subtractBits (lengthBits W F).value (lengthBits W ss).value).value
  (encode W q) dw (by simp)).2.1
 simp only [Refines] at a ⊢
 simp only [bitAccepted,meterAccepted]
 constructor
 · rw [a.1,leBits_value,subtractBits_value,fv,sv,encode_value W q qFit]
   rfl
 · simp only [Nat.mul_add,Nat.mul_comm (beta W) 4]
   have extra : (lengthBits W F).work+(lengthBits W ss).work+
    (subtractBits (lengthBits W F).value (lengthBits W ss).value).work+
    (leBits (subtractBits (lengthBits W F).value (lengthBits W ss).value).value (encode W q)).work≤
    beta W*(6*(F.length+ss.length+1)) := by
    dsimp only [beta]
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm W 6,Nat.mul_one] at fw sw ⊢
    omega
   simp only [Nat.mul_add] at extra
   omega

def bitChecked (W : Nat) (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest) : Charged (Option Forest) :=
 let a:=bitAccepted W T ss q F
 ⟨if a.value then some F else none,a.work+2*beta W⟩

theorem bitChecked_refines (W : Nat) (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest)
 (positive : 1≤W) (tc : TargetCap W T) (sc : SourcesCap W ss) (fc : LabelCap W F.flatten)
 (sourceFit : (ss.map leaves).flatten.length<2^W) (cellsFit : F.flatten.length<2^W)
 (fFit : F.length<2^W) (sFit : ss.length<2^W) (qFit : q<2^W) :
 Refines W (bitChecked W T ss q F) (meterChecked T ss q F) := by
 have a:=bitAccepted_refines W T ss q F positive tc sc fc sourceFit cellsFit fFit sFit qFit
 simp only [Refines] at a ⊢
 simp only [bitChecked,meterChecked,a.1]
 refine ⟨by trivial,?_⟩
 simp only [Nat.mul_add,Nat.mul_comm (beta W) 2];omega
end GenericForest.ScalarBits
