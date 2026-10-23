import ProducerCostRawLedger
set_option maxRecDepth 2048
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork
variable {P A : Type}
def runCallbackWork (solve : P→Bits→Charged (Option (Bits×A))) (b : Bits) : List (Job P A)→Nat
 | []=>0
 | .resolved _ _ _::js=>runCallbackWork solve b js
 | .hard p::js=>let a:=solve p b
  a.work+(match a.value with | none=>0 | some _=>runCallbackWork solve b js)
theorem runBits_ledger (solve : P→Bits→Charged (Option (Bits×A))) (b : Bits) (js : List (Job P A)) :
 (runBits solve b js).work≤runCallbackWork solve b js+(12*(js.length+1)+8)*(js.length+1) := by
 induction js with
 | nil=>simp [runBits,runCallbackWork]
 | cons j js ih=>
  have rw:=(runBits_storage solve b js).1
  have aw:=addCarry_work (runBits solve b js).value.visits [] true
  cases j with
  | resolved p c a=>
   simp only [runBits,runCallbackWork,incrementBits,List.length_nil,List.length_cons] at *
   simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at *;omega
  | hard p=>
   cases h : (solve p b).value <;> simp only [runBits,runCallbackWork,h,incrementBits,List.length_nil,List.length_cons] at *
   all_goals simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at *;omega

def scheduleCallbackWork (solve : P→Bits→Charged (Option (Bits×A))) (q : Bits) (js : List (Job P A)) : Nat:=
 let k:=knownBits js;let p:=pendingBits js;let twice:=addBits p.value p.value
 let threshold:=addBits k.value twice.value;let enough:=leBits threshold.value q
 if enough.value then runCallbackWork solve (allocationBits q k.value p.value).value js else 0
theorem scheduleBits_ledger (solve : P→Bits→Charged (Option (Bits×A))) (q : Bits)
 (js : List (Job P A)) (W : Nat) (caps : ∀j∈js,CostWidth W j)
 (answerCap : ∀p b x,(solve p b).value=some x→x.1.length≤W) :
 (scheduleBits solve q js).work≤scheduleCallbackWork solve q js+1000*(q.length+W+js.length+3)*(js.length+1) := by
 have kw:=knownBits_width W js caps;have pw:=pendingBits_width js
 have kc:=knownBits_work W js caps;have pc:=pendingBits_work js
 have tw:=addCarry_length (pendingBits js).value (pendingBits js).value false
 have tc:=addCarry_work (pendingBits js).value (pendingBits js).value false
 have hw:=addCarry_length (knownBits js).value (addBits (pendingBits js).value (pendingBits js).value).value false
 have hc:=addCarry_work (knownBits js).value (addBits (pendingBits js).value (pendingBits js).value).value false
 have ec:=(compare_family_work (addBits (knownBits js).value (addBits (pendingBits js).value (pendingBits js).value).value).value q).2.1
 have bc:=allocationBits_work q (knownBits js).value (pendingBits js).value
 let b:=(allocationBits q (knownBits js).value (pendingBits js).value).value
 have rc:=runBits_ledger solve b js
 let C:=runCallbackWork solve b js
 have rs:=runBits_storage solve b js
 let X:=q.length+W+js.length+3
 have kcost : (knownBits js).work≤(28*X)*(js.length+1):=Nat.le_trans kc (Nat.mul_le_mul_right _ (by dsimp [X];omega))
 have pcost : (pendingBits js).work≤(16*X)*(js.length+1):=Nat.le_trans pc (Nat.mul_le_mul_right _ (by dsimp [X];omega))
 have rcost : (runBits solve b js).work≤C+20*X*(js.length+1):=Nat.le_trans rc (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by dsimp [X];omega)) C)
 have acbound : (allocationBits q (knownBits js).value (pendingBits js).value).work≤400*X:=by dsimp [X];omega
 have scalar : (addBits (pendingBits js).value (pendingBits js).value).work+
  (addBits (knownBits js).value (addBits (pendingBits js).value (pendingBits js).value).value).work+
  (leBits (addBits (knownBits js).value (addBits (pendingBits js).value (pendingBits js).value).value).value q).work≤100*X:=by
  dsimp [X];simp only [addBits,Nat.max_self] at *;omega
 have absorb : X≤X*(js.length+1):=by simp only [Nat.mul_add,Nat.mul_one];omega
 clear kc pc rc tc hc ec bc tw hw rs
 dsimp only [scheduleBits,scheduleCallbackWork]
 split
 · cases hx : (runBits solve b js).value.answers with
   | none=>
    dsimp only [b] at rcost
    change _+_+_+_+_+12+_+_+4+4≤_
    change _≤C+1000*X*(js.length+1)
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
    change _≤C+1000*X*(js.length+1)
    simp only [Nat.add_mul,Nat.mul_assoc] at kcost pcost rcost acost ⊢
    omega
 · rename_i rejected
   simp only [rejected,ite_false,Nat.zero_add]
   change _+_+_+_+_+12+4≤_
   change _≤1000*X*(js.length+1)
   simp only [Nat.add_mul,Nat.mul_assoc] at kcost pcost ⊢
   omega

end GenericForest.BinaryProducer
