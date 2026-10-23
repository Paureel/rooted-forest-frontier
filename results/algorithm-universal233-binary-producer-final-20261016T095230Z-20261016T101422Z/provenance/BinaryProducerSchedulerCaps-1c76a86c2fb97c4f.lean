import BinaryProducerScheduler
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork
variable {P A : Type}
def CostWidth (W : Nat) : Job P A→Prop
 | .resolved _ c _=>c.length≤W | .hard _=>True

theorem knownBits_width (W : Nat) (js : List (Job P A)) (cap : ∀j∈js,CostWidth W j) :
 (knownBits js).value.length≤W+js.length := by
 induction js with
 | nil=>simp [knownBits]
 | cons j js ih=>
  have r:=ih (fun j h=>cap j (by simp [h]))
  have costcap:=cap j (by simp)
  cases j with
  | hard p=>simp only [knownBits,List.length_cons];omega
  | resolved p c a=>
   have v:=addCarry_length c (knownBits js).value false
   simp only [knownBits,addBits,List.length_cons,CostWidth] at *;omega

theorem pendingBits_width (js : List (Job P A)) : (pendingBits js).value.length≤js.length := by
 induction js with
 | nil=>simp [pendingBits]
 | cons j js ih=>
  cases j with
  | resolved p c a=>simp only [pendingBits,List.length_cons];omega
  | hard p=>have a:=addCarry_length (pendingBits js).value [] true
            simp only [pendingBits,incrementBits,List.length_nil,Nat.max_zero,List.length_cons] at *;omega

theorem answerBits_width (W : Nat) (xs : List (Bits×A)) (cap : ∀x∈xs,x.1.length≤W) :
 (answerBits xs).value.length≤W+xs.length := by
 induction xs with
 | nil=>simp [answerBits]
 | cons x xs ih=>
  have r:=ih (fun x h=>cap x (by simp [h]));have c:=cap x (by simp)
  have a:=addCarry_length x.1 (answerBits xs).value false
  rcases x with ⟨c,v⟩
  simp only [answerBits,addBits,List.length_cons] at *;omega

theorem knownBits_work (W : Nat) (js : List (Job P A)) (cap : ∀j∈js,CostWidth W j) :
 (knownBits js).work≤(24*(W+js.length+1)+4)*(js.length+1) := by
 induction js with
 | nil=>simp [knownBits] <;> omega
 | cons j js ih=>
  have costcap:=cap j (by simp)
  have cc : ∀j∈js,CostWidth W j:=fun j h=>cap j (by simp [h])
  have r:=ih cc;have rw:=knownBits_width W js cc
  cases j with
  | hard p=>simp only [knownBits,List.length_cons];simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at *;omega
  | resolved p c a=>
   have aw:=addCarry_work c (knownBits js).value false
   simp only [knownBits,addBits,List.length_cons,CostWidth] at *
   simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at *;omega

theorem pendingBits_work (js : List (Job P A)) :
 (pendingBits js).work≤(12*(js.length+1)+4)*(js.length+1) := by
 induction js with
 | nil=>simp [pendingBits]
 | cons j js ih=>
  have rw:=pendingBits_width js
  cases j with
  | resolved p c a=>simp only [pendingBits,List.length_cons];simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at *;omega
  | hard p=>
   have aw:=addCarry_work (pendingBits js).value [] true
   simp only [pendingBits,incrementBits,List.length_cons,List.length_nil] at *
   simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at *;omega

theorem answerBits_work (W : Nat) (xs : List (Bits×A)) (cap : ∀x∈xs,x.1.length≤W) :
 (answerBits xs).work≤(24*(W+xs.length+1)+4)*(xs.length+1) := by
 induction xs with
 | nil=>simp [answerBits] <;> omega
 | cons x xs ih=>
  have cc : ∀x∈xs,x.1.length≤W:=fun x h=>cap x (by simp [h])
  have r:=ih cc;have rw:=answerBits_width W xs cc;have c:=cap x (by simp)
  have aw:=addCarry_work x.1 (answerBits xs).value false
  rcases x with ⟨c,v⟩
  simp only [answerBits,addBits,List.length_cons] at *
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at *;omega

theorem runBits_storage (solve : P→Bits→Charged (Option (Bits×A))) (b : Bits) (js : List (Job P A)) :
 (runBits solve b js).value.visits.length≤js.length ∧
 (runBits solve b js).value.calls.length≤js.length ∧
 (∀xs,(runBits solve b js).value.answers=some xs→xs.length≤js.length) ∧
 (∀c∈(runBits solve b js).value.calls,c=b) := by
 induction js with
 | nil=>simp [runBits]
 | cons j js ih=>
  have iw:=addCarry_length (runBits solve b js).value.visits [] true
  cases j with
  | resolved p c a=>
   simp only [runBits,incrementBits,List.length_nil,Nat.max_zero,List.length_cons] at *
   refine ⟨by omega,by omega,?_,ih.2.2.2⟩
   intro xs hx
   cases h : (runBits solve b js).value.answers with
   | none=>simp [h] at hx
   | some ys=>simp only [h,Option.map_some,Option.some.injEq] at hx;subst xs;have hh:=ih.2.2.1 ys h;simp;omega
  | hard p=>
   cases h : (solve p b).value with
   | none=>simp [runBits,h]
   | some x=>
    simp only [runBits,h,incrementBits,List.length_nil,Nat.max_zero,List.length_cons] at *
    refine ⟨by omega,by omega,?_,?_⟩
    · intro xs hx
      cases ha : (runBits solve b js).value.answers with
      | none=>simp [ha] at hx
      | some ys=>simp only [ha,Option.map_some,Option.some.injEq] at hx;subst xs;have hh:=ih.2.2.1 ys ha;simp;omega
    · intro c hc;rcases List.mem_cons.mp hc with hc|hc
      · exact hc
      · exact ih.2.2.2 c hc

theorem runBits_answerCap (solve : P→Bits→Charged (Option (Bits×A))) (b : Bits)
 (Good : Bits×A→Prop) (js : List (Job P A))
 (resolved : ∀p c a,Job.resolved p c a∈js→Good (c,a))
 (hard : ∀p x,(solve p b).value=some x→Good x) :
 ∀xs,(runBits solve b js).value.answers=some xs→∀x∈xs,Good x := by
 induction js with
 | nil=>simp [runBits]
 | cons j js ih=>
  have rr:=ih (fun p c a h=>resolved p c a (by simp [h]))
  cases j with
  | resolved p c a=>
   intro xs hx
   cases h : (runBits solve b js).value.answers with
   | none=>simp [runBits,h] at hx
   | some ys=>
    simp only [runBits,h,Option.map_some,Option.some.injEq] at hx;subst xs
    intro x hx;rcases List.mem_cons.mp hx with rfl|hx
    · exact resolved p c a (by simp)
    · exact rr ys h x hx
  | hard p=>
   cases h : (solve p b).value with
   | none=>simp [runBits,h]
   | some x=>
    intro xs hx
    cases ha : (runBits solve b js).value.answers with
    | none=>simp [runBits,h,ha] at hx
    | some ys=>
     simp only [runBits,h,ha,Option.map_some,Option.some.injEq] at hx;subst xs
     intro y hy;rcases List.mem_cons.mp hy with rfl|hy
     · exact hard p _ h
     · exact rr ys ha y hy

/-- C bounds each actual recursive callback at this represented budget. It is
an explicit modular callback premise, not an assumed whole-solver cost. -/
theorem runBits_work (solve : P→Bits→Charged (Option (Bits×A))) (b : Bits) (js : List (Job P A))
 (C : Nat) (callback : ∀p,(solve p b).work≤C) :
 (runBits solve b js).work≤(C+12*(js.length+1)+8)*(js.length+1) := by
 induction js with
 | nil=>simp [runBits] <;> omega
 | cons j js ih=>
  have rw:=(runBits_storage solve b js).1
  have aw:=addCarry_work (runBits solve b js).value.visits [] true
  cases j with
  | resolved p c a=>
   simp only [runBits,incrementBits,List.length_nil,List.length_cons] at *
   simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at *;omega
  | hard p=>
   have cw:=callback p
   cases h : (solve p b).value <;> simp only [runBits,h,incrementBits,List.length_nil,List.length_cons] at *
   all_goals simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at *;omega
end GenericForest.BinaryProducer
