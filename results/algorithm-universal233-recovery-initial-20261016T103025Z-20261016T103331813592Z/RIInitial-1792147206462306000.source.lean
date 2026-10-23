import RIBuild
namespace OrdinaryDispatch.RecoveryInitialBits
open RMAF Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits

abbrev InitValue := Option (List Bool×BitTree)
/-- Specification only; never called by a represented producer. -/
def viewInit (r : InitValue) : Option (Nat×GTree) := r.map (fun p=>(decode p.1,viewTree p.2))

def initialCore (W : Nat) (t : InputTree) (P : List (List (List Bool))) (budget : List Bool) : Charged InitValue :=
 let a:=leafArrays t;let proper:=ownedNodup a.value;let ca:=closeArrays a.value
 if proper.value then
  let b:=leafArrays t;let q:=clipOwned W budget b.value;let tree:=build P [] t
  let cb:=closeArrays b.value
  ⟨some (q.value,tree.value),a.work+proper.work+ca.work+b.work+q.work+tree.work+cb.work+16⟩
 else ⟨none,a.work+proper.work+ca.work+8⟩

@[simp] theorem initialCore_value (W : Nat) (t : InputTree) (P : List (List (List Bool))) (budget : List Bool)
 (fits : (inputLeaves t).length<2^W) :
 viewInit (initialCore W t P budget).value=
 (OrdinaryDispatch.RecoveryLocalWork.meterInitial (OrdinaryDispatch.RecoveryLocalWork.meterColor (P.map (List.map decode)))
  (decode budget) (viewInput t)).value := by
 by_cases h:(leaves (viewInput t)).Nodup
 · simp [initialCore,viewInit,OrdinaryDispatch.RecoveryLocalWork.meterInitial_value,h,
    clipOwned_value W budget (inputLeaves t) fits]
 · simp [initialCore,viewInit,OrdinaryDispatch.RecoveryLocalWork.meterInitial_value,h]

/-- Copies supplied stored finite-bit inputs, executes the literal initializer,
then pays scope-close traversals for all owned input copies. No encoding/view
function occurs in this runtime body. -/
def initialize (W : Nat) (t : InputTree) (P : List (List (List Bool))) (budget : List Bool) : Charged InitValue :=
 let ti:=copyInput t;let pi:=copyForest P;let bi:=copyBits budget
 let r:=initialCore W ti.value pi.value bi.value
 let ct:=closeInput ti.value;let cp:=closeForest pi.value;let cb:=closeBits bi.value
 ⟨r.value,ti.work+pi.work+bi.work+r.work+ct.work+cp.work+cb.work+16⟩

@[simp] theorem initialize_value (W : Nat) (t : InputTree) (P : List (List (List Bool))) (budget : List Bool)
 (fits : (inputLeaves t).length<2^W) :
 viewInit (initialize W t P budget).value=
 (OrdinaryDispatch.RecoveryLocalWork.meterInitial (OrdinaryDispatch.RecoveryLocalWork.meterColor (P.map (List.map decode)))
  (decode budget) (viewInput t)).value := by
 simpa only [initialize,copyInput_value,copyForest_value,copyBits_value] using initialCore_value W t P budget fits

theorem initialCore_work (W N : Nat) (t : InputTree) (P : List (List (List Bool))) (budget : List Bool)
 (positive : 1≤W) (tw : InputWords W t) (pw : ForestWords W P) (bw : budget.length≤W)
 (tn : inputNodes t≤N) (pn : P.flatten.length+P.length≤N) :
 (initialCore W t P budget).work≤1024*(W+1)*(N+1)^2 := by
 let V:=W+1;let K:=(W+1)*(N+1)^2
 have leaves:=leafArrays_work W N t tw tn
 have len: (inputLeaves t).length≤N:=Nat.le_trans (inputLeaves_length t) tn
 have words:=inputLeaves_words W t tw
 have dup:=ownedNodup_work W (inputLeaves t) words
 have close:=closeArrays_work (inputLeaves t)
 have cells:=arrayCells_bound W (inputLeaves t) words
 have clip:=clipOwned_work W budget (inputLeaves t) positive bw
 have built:=build_work W N P [] t tw pw (by simpa)
 have sq:(N+1)≤(N+1)^2:=by
  rw [Nat.pow_two];simpa only [Nat.one_mul] using Nat.mul_le_mul_right (N+1) (show 1≤N+1 by omega)
 have vk:V*(N+1)≤K:=Nat.mul_le_mul_left V sq
 have kp:1≤K:=by
  dsimp only [K];have p:1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
  have a:=Nat.mul_le_mul (show 1≤W+1 by omega) p;simpa using a
 have leafa:(leafArrays t).work≤32*K:=by
  have scale:=Nat.mul_le_mul_left (32*(W+1)*(N+1)) (Nat.le_trans tn (Nat.le_succ N))
  have eq:32*(W+1)*(N+1)*(N+1)=32*K:=by simp only [K,Nat.pow_two,Nat.mul_assoc]
  rw [eq] at scale;omega
 have dupa:(ownedNodup (inputLeaves t)).work≤128*K:=by
  have scale:=Nat.mul_le_mul_left (128*(W+1)) (Nat.pow_le_pow_left (Nat.add_le_add_right len 1) 2)
  change _≤128*K at scale
  omega
 have closea:(closeArrays (inputLeaves t)).work≤16*K:=by
  have scale:=Nat.mul_le_mul_left (W+1) (Nat.add_le_add_right len 1)
  have vpos:1≤V:=by dsimp [V];omega
  simp only [Nat.mul_add,Nat.mul_one] at scale
  have expand:16*K=16* K:=rfl
  dsimp only [V] at vk
  omega
 have clipa:(clipOwned W budget (inputLeaves t)).work≤256*K:=by
  have scale:=Nat.mul_le_mul_left (256*(W+1)) (Nat.add_le_add_right len 1)
  have eq:256*(W+1)*(N+1)=256*(V*(N+1)):=by dsimp [V];ac_rfl
  rw [eq] at scale
  have kscale:=Nat.mul_le_mul_left 256 vk
  omega
 have builda:(build P [] t).work≤224*K:=by
  have cap:buildCap W N P≤224*(W+1)*(N+1):=by
   have s:=Nat.mul_le_mul_left (160*(W+1)) (Nat.add_le_add_right pn 1)
   simp only [buildCap];omega
  have scale:=Nat.mul_le_mul cap (Nat.le_trans tn (Nat.le_succ N))
  have eq:224*(W+1)*(N+1)*(N+1)=224*K:=by simp only [K,Nat.pow_two,Nat.mul_assoc]
  rw [eq] at scale
  omega
 simp only [initialCore,leafArrays_value]
 split <;> simp only [Charged.work]
 · change _≤1024*K;omega
 · change _≤1024*K;omega

theorem initialize_work (W N : Nat) (t : InputTree) (P : List (List (List Bool))) (budget : List Bool)
 (positive : 1≤W) (tw : InputWords W t) (pw : ForestWords W P) (bw : budget.length≤W)
 (tn : inputNodes t≤N) (pn : P.flatten.length+P.length≤N) :
 (initialize W t P budget).work≤2048*(W+1)*(N+1)^2 := by
 have core:=initialCore_work W N t P budget positive tw pw bw tn pn
 have ti:=copyInput_work W t tw;have ct:=closeInput_work W t tw
 have pi:=copyForest_work P;have cp:=closeForest_work P
 have cells:=forestCells_bound W P pw
 let K:=(W+1)*(N+1)^2
 have sq:N+1≤(N+1)^2:=by rw [Nat.pow_two];simpa only [Nat.one_mul] using Nat.mul_le_mul_right (N+1) (show 1≤N+1 by omega)
 have vk:(W+1)*(N+1)≤K:=Nat.mul_le_mul_left (W+1) sq
 have v:W+1≤K:=by
  have a:=Nat.mul_le_mul_left (W+1) (show 1≤N+1 by omega)
  simp only [Nat.mul_one] at a;omega
 have nf:forestCells P+1≤2*((W+1)*(N+1)):=by
  have a:=Nat.mul_le_mul_left (W+1) (show P.flatten.length≤N by omega)
  have b:=Nat.mul_le_mul_right (N+1) (show 1≤W+1 by omega)
  simp only [Nat.mul_add,Nat.mul_one,Nat.one_mul] at a b ⊢
  omega
 have pi32:(copyForest P).work≤32*K:=by have a:=Nat.mul_le_mul_left 16 nf;omega
 have cp32:(closeForest P).work≤32*K:=by have a:=Nat.mul_le_mul_left 16 nf;omega
 have ti16:(copyInput t).work≤16*K:=by
  have a:=Nat.mul_le_mul_left (16*(W+1)) (Nat.le_trans tn (Nat.le_succ N))
  have b:=Nat.mul_le_mul_left 16 vk
  simp only [Nat.mul_assoc] at a b;omega
 have ct16:(closeInput t).work≤16*K:=by
  have a:=Nat.mul_le_mul_left (16*(W+1)) (Nat.le_trans tn (Nat.le_succ N))
  have b:=Nat.mul_le_mul_left 16 vk
  simp only [Nat.mul_assoc] at a b;omega
 change (initialCore W t P budget).work≤1024*K at core
 simp only [initialize,copyInput_value,copyForest_value,copyBits_value,copyBits_work,closeBits_work]
 change _≤2048*K
 omega
end OrdinaryDispatch.RecoveryInitialBits
