import BinaryProducerSchedulerCaps
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork
variable {P A : Type}
theorem allocationBits_width (q k p : Bits) :
 (allocationBits q k p).value.length≤q.length+k.length+p.length+2 := by
 have pm:=subtractBits_length p [true]
 have pt:=addCarry_length (subtractBits p [true]).value (subtractBits p [true]).value false
 have qk:=subtractBits_length q k
 have b:=subtractBits_length (subtractBits q k).value
  (addBits (subtractBits p [true]).value (subtractBits p [true]).value).value
 simp only [allocationBits,addBits,List.length_cons,List.length_nil] at *;omega

theorem allocationBits_work (q k p : Bits) :
 (allocationBits q k p).work≤200*(q.length+k.length+p.length+3) := by
 have pm:=subtractBits_length p [true]
 have pt:=addCarry_length (subtractBits p [true]).value (subtractBits p [true]).value false
 have qk:=subtractBits_length q k
 have a:=subtractBits_work p [true]
 have b:=addCarry_work (subtractBits p [true]).value (subtractBits p [true]).value false
 have c:=subtractBits_work q k
 have d:=subtractBits_work (subtractBits q k).value
  (addBits (subtractBits p [true]).value (subtractBits p [true]).value).value
 simp only [allocationBits,addBits,List.length_cons,List.length_nil] at *;omega

/-- Storage is bounded in terms of actual stored input widths and job count.
No logarithmic or original-input global invariant is assumed here. -/
theorem allocated_local_width (W : Nat) (q : Bits) (js : List (Job P A))
 (caps : ∀j∈js,CostWidth W j) :
 (allocationBits q (knownBits js).value (pendingBits js).value).value.length≤q.length+W+2*js.length+2 := by
 have a:=allocationBits_width q (knownBits js).value (pendingBits js).value
 have k:=knownBits_width W js caps;have p:=pendingBits_width js;omega

/-- Explicit per-call C and result-cost W contracts are modular obligations.
All actual setup, arithmetic and list/receipt allocations are included. -/
theorem scheduleBits_work (solve : P→Bits→Charged (Option (Bits×A))) (q : Bits)
 (js : List (Job P A)) (W C : Nat) (caps : ∀j∈js,CostWidth W j)
 (callback : ∀p b,(solve p b).work≤C)
 (answerCap : ∀p b x,(solve p b).value=some x→x.1.length≤W) :
 (scheduleBits solve q js).work≤(C+1000*(q.length+W+js.length+3))*(js.length+1) := by
 have kw:=knownBits_width W js caps;have pw:=pendingBits_width js
 have kc:=knownBits_work W js caps;have pc:=pendingBits_work js
 have tw:=addCarry_length (pendingBits js).value (pendingBits js).value false
 have tc:=addCarry_work (pendingBits js).value (pendingBits js).value false
 have hw:=addCarry_length (knownBits js).value (addBits (pendingBits js).value (pendingBits js).value).value false
 have hc:=addCarry_work (knownBits js).value (addBits (pendingBits js).value (pendingBits js).value).value false
 have ec:=(compare_family_work (addBits (knownBits js).value (addBits (pendingBits js).value (pendingBits js).value).value).value q).2.1
 have bc:=allocationBits_work q (knownBits js).value (pendingBits js).value
 let b:=(allocationBits q (knownBits js).value (pendingBits js).value).value
 have rc:=runBits_work solve b js C (fun p=>callback p b)
 have rs:=runBits_storage solve b js
 let X:=q.length+W+js.length+3
 have kcost : (knownBits js).work≤(28*X)*(js.length+1):=Nat.le_trans kc (Nat.mul_le_mul_right _ (by dsimp [X];omega))
 have pcost : (pendingBits js).work≤(16*X)*(js.length+1):=Nat.le_trans pc (Nat.mul_le_mul_right _ (by dsimp [X];omega))
 have rcost : (runBits solve b js).work≤(C+20*X)*(js.length+1):=Nat.le_trans rc (Nat.mul_le_mul_right _ (by dsimp [X];omega))
 have acbound : (allocationBits q (knownBits js).value (pendingBits js).value).work≤400*X:=by dsimp [X];omega
 have scalar : (addBits (pendingBits js).value (pendingBits js).value).work+
  (addBits (knownBits js).value (addBits (pendingBits js).value (pendingBits js).value).value).work+
  (leBits (addBits (knownBits js).value (addBits (pendingBits js).value (pendingBits js).value).value).value q).work≤100*X:=by
  dsimp [X];simp only [addBits,Nat.max_self] at *;omega
 have absorb : X≤X*(js.length+1):=by simp only [Nat.mul_add,Nat.mul_one];omega
 clear kc pc rc tc hc ec bc tw hw rs
 dsimp only [scheduleBits]
 split
 · cases hx : (runBits solve b js).value.answers with
   | none=>
    dsimp only [b] at rcost
    change _+_+_+_+_+12+_+_+4+4≤_
    change _≤(C+1000*X)*(js.length+1)
    simp only [Nat.add_mul,Nat.mul_assoc] at kcost pcost rcost ⊢
    omega
   | some xs=>
    have storage:=runBits_storage solve b js
    have xl:=storage.2.2.1 xs hx
    have xc : ∀x∈xs,x.1.length≤W:=runBits_answerCap solve b (fun x=>x.1.length≤W) js
      (fun p c a h=>by have hh:=caps (.resolved p c a) h;exact hh)
      (fun p x h=>answerCap p b x h) xs hx
    have aw:=answerBits_width W xs xc;have ac:=answerBits_work W xs xc
    have fc:=(compare_family_work (answerBits xs).value q).2.1
    have acost : (answerBits xs).work≤(28*X)*(js.length+1):=by
     exact Nat.le_trans ac (Nat.mul_le_mul (by dsimp [X];omega) (by omega))
    have fcost : (leBits (answerBits xs).value q).work≤10*X:=by dsimp [X];omega
    dsimp only [b] at rcost
    change _+_+_+_+_+12+_+_+4+_+_+4≤_
    change _≤(C+1000*X)*(js.length+1)
    simp only [Nat.add_mul,Nat.mul_assoc] at kcost pcost rcost acost ⊢
    omega
 · change _+_+_+_+_+12+4≤_
   change _≤(C+1000*X)*(js.length+1)
   simp only [Nat.add_mul,Nat.mul_assoc] at kcost pcost ⊢
   omega

end GenericForest.BinaryProducer
