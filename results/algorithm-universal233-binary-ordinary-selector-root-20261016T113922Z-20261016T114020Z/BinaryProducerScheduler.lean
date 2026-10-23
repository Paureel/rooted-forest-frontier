import BinaryCallerOrdinaryBounds
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork
variable {P P' A A' : Type}

theorem nativeReceipt_ext {a b : Universal233.PaidQueries.Receipt A} (h : a.answers=b.answers) (c : a.calls=b.calls) (v : a.visits=b.visits) : a=b := by
 cases a;cases b;simp_all

/-- Costs are persistent little-endian bits. Problems and answers are shared
immutable values; newly constructed list and receipt nodes are charged below. -/
inductive Job (P A : Type) where
 | resolved (problem : P) (cost : Bits) (answer : A)
 | hard (problem : P)
 deriving Repr
structure Receipt (A : Type) where
 answers : Option (List (Bits × A))
 calls : List Bits
 visits : Bits
 deriving Repr

def jobValue (π : P→P') (ρ : A→A') : Job P A→Universal233.PaidQueries.Job P' A'
 | .resolved p c a=>.resolved (π p) (decode c) (ρ a)
 | .hard p=>.hard (π p)
def pairValue (ρ : A→A') (x : Bits×A) : Nat×A':=(decode x.1,ρ x.2)
def receiptValue (ρ : A→A') (r : Receipt A) : Universal233.PaidQueries.Receipt A':=
 ⟨r.answers.map (List.map (pairValue ρ)),r.calls.map decode,decode r.visits⟩

def knownBits : List (Job P A)→Charged Bits
 | []=>⟨[],1⟩
 | .resolved _ c _::js=>let r:=knownBits js;let a:=addBits c r.value;⟨a.value,r.work+a.work+4⟩
 | .hard _::js=>let r:=knownBits js;⟨r.value,r.work+4⟩
def pendingBits : List (Job P A)→Charged Bits
 | []=>⟨[],1⟩
 | .resolved _ _ _::js=>let r:=pendingBits js;⟨r.value,r.work+4⟩
 | .hard _::js=>let r:=pendingBits js;let a:=incrementBits r.value;⟨a.value,r.work+a.work+4⟩
def answerBits : List (Bits×A)→Charged Bits
 | []=>⟨[],1⟩
 | (c,_)::xs=>let r:=answerBits xs;let a:=addBits c r.value;⟨a.value,r.work+a.work+4⟩

@[simp] theorem knownBits_value (π : P→P') (ρ : A→A') (js : List (Job P A)) :
 decode (knownBits js).value=Universal233.PaidQueries.knownCost (js.map (jobValue π ρ)) := by
 induction js with
 | nil=>rfl
 | cons j js ih=>cases j <;> simp [knownBits,jobValue,Universal233.PaidQueries.knownCost,ih]
@[simp] theorem pendingBits_value (π : P→P') (ρ : A→A') (js : List (Job P A)) :
 decode (pendingBits js).value=Universal233.PaidQueries.pending (js.map (jobValue π ρ)) := by
 induction js with
 | nil=>rfl
 | cons j js ih=>cases j <;> simp [pendingBits,jobValue,Universal233.PaidQueries.pending,ih,Nat.add_comm]
@[simp] theorem answerBits_value (ρ : A→A') (xs : List (Bits×A)) :
 decode (answerBits xs).value=Universal233.PaidQueries.answerCost (xs.map (pairValue ρ)) := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>rcases x with ⟨c,a⟩;simp only [Universal233.PaidQueries.answerCost,List.map_map] at ih;simp [answerBits,pairValue,Universal233.PaidQueries.answerCost,ih]

def runBits (solve : P→Bits→Charged (Option (Bits×A))) (b : Bits) : List (Job P A)→Charged (Receipt A)
 | []=>⟨⟨some [],[],[]⟩,4⟩
 | .resolved _ c a::js=>
  let r:=runBits solve b js;let v:=incrementBits r.value.visits
  ⟨⟨r.value.answers.map ((c,a)::·),r.value.calls,v.value⟩,r.work+v.work+8⟩
 | .hard p::js=>
  let s:=solve p b
  match s.value with
  | none=>⟨⟨none,[b],[true]⟩,s.work+8⟩
  | some x=>let r:=runBits solve b js;let v:=incrementBits r.value.visits
            ⟨⟨r.value.answers.map (x::·),b::r.value.calls,v.value⟩,s.work+r.work+v.work+8⟩

theorem runBits_value (π : P→P') (ρ : A→A')
 (solve : P→Bits→Charged (Option (Bits×A))) (native : P'→Nat→Option (Nat×A'))
 (ih : ∀p b,(solve p b).value.map (pairValue ρ)=native (π p) (decode b)) (b : Bits) (js : List (Job P A)) :
 receiptValue ρ (runBits solve b js).value=Universal233.PaidQueries.run native (decode b) (js.map (jobValue π ρ)) := by
 induction js with
 | nil=>rfl
 | cons j js rec=>
  cases j with
  | resolved p c a=>
   have aa:=congrArg Universal233.PaidQueries.Receipt.answers rec
   have cc:=congrArg Universal233.PaidQueries.Receipt.calls rec
   have vv:=congrArg Universal233.PaidQueries.Receipt.visits rec
   apply nativeReceipt_ext
   · simpa [runBits,receiptValue,jobValue,Universal233.PaidQueries.run,Option.map_map,List.map_cons,pairValue,Function.comp_def] using
       congrArg (Option.map ((decode c,ρ a)::·)) aa
   · simpa [runBits,receiptValue,jobValue,Universal233.PaidQueries.run] using cc
   · simpa [runBits,receiptValue,jobValue,Universal233.PaidQueries.run] using vv
  | hard p=>
   have h:=ih p b
   cases hs : (solve p b).value with
   | none=>simp [hs] at h;simp [runBits,hs,jobValue,Universal233.PaidQueries.run,←h,receiptValue,decode,bit]
   | some x=>
    simp only [hs,Option.map_some] at h
    have aa:=congrArg Universal233.PaidQueries.Receipt.answers rec
    have cc:=congrArg Universal233.PaidQueries.Receipt.calls rec
    have vv:=congrArg Universal233.PaidQueries.Receipt.visits rec
    apply nativeReceipt_ext
    · simpa [runBits,hs,receiptValue,jobValue,Universal233.PaidQueries.run,←h,Option.map_map,pairValue,Function.comp_def] using
        congrArg (Option.map (pairValue ρ x::·)) aa
    · simpa [runBits,hs,receiptValue,jobValue,Universal233.PaidQueries.run,←h] using congrArg (decode b::·) cc
    · simpa [runBits,hs,receiptValue,jobValue,Universal233.PaidQueries.run,←h] using vv

def allocationBits (q k p : Bits) : Charged Bits :=
 let pm:=subtractBits p [true];let pt:=addBits pm.value pm.value
 let qk:=subtractBits q k;let budget:=subtractBits qk.value pt.value
 ⟨budget.value,pm.work+pt.work+qk.work+budget.work+8⟩
@[simp] theorem allocationBits_value (q k p : Bits) :
 decode (allocationBits q k p).value=decode q-decode k-2*(decode p-1) := by
 simp [allocationBits,subtractBits_value,decode,bit,Nat.two_mul]

/-- The allocated budget spine is shared immutably across recursive calls. -/
def scheduleBits (solve : P→Bits→Charged (Option (Bits×A))) (q : Bits) (js : List (Job P A)) : Charged (Receipt A):=
 let k:=knownBits js;let p:=pendingBits js;let twice:=addBits p.value p.value
 let threshold:=addBits k.value twice.value;let enough:=leBits threshold.value q
 let setup:=k.work+p.work+twice.work+threshold.work+enough.work+12
 if enough.value then
  let budget:=allocationBits q k.value p.value
  let r:=runBits solve budget.value js
  let overhead:=setup+budget.work+r.work+4
  match r.value.answers with
  | none=>⟨⟨none,r.value.calls,r.value.visits⟩,overhead+4⟩
  | some xs=>let a:=answerBits xs;let fits:=leBits a.value q
             ⟨⟨if fits.value then some xs else none,r.value.calls,r.value.visits⟩,overhead+a.work+fits.work+4⟩
 else ⟨⟨none,[],[]⟩,setup+4⟩

theorem scheduleBits_value (π : P→P') (ρ : A→A')
 (solve : P→Bits→Charged (Option (Bits×A))) (native : P'→Nat→Option (Nat×A'))
 (ih : ∀p b,(solve p b).value.map (pairValue ρ)=native (π p) (decode b)) (q : Bits) (js : List (Job P A)) :
 receiptValue ρ (scheduleBits solve q js).value=Universal233.PaidQueries.schedule native (decode q) (js.map (jobValue π ρ)) := by
 have k:=knownBits_value π ρ js;have p:=pendingBits_value π ρ js
 have threshold : (leBits (addBits (knownBits js).value (addBits (pendingBits js).value (pendingBits js).value).value).value q).value=
   decide (Universal233.PaidQueries.knownCost (js.map (jobValue π ρ))+2*Universal233.PaidQueries.pending (js.map (jobValue π ρ))≤decode q):=by
  simp [leBits_value,k,p,Nat.two_mul]
 have budget : decode (allocationBits q (knownBits js).value (pendingBits js).value).value=
   Universal233.PaidQueries.allocated (decode q) (js.map (jobValue π ρ)):=by
  simp [k,p,Universal233.PaidQueries.allocated]
 have r:=runBits_value π ρ solve native ih (allocationBits q (knownBits js).value (pendingBits js).value).value js
 rw [budget] at r
 have aa:=congrArg Universal233.PaidQueries.Receipt.answers r
 have cc:=congrArg Universal233.PaidQueries.Receipt.calls r
 have vv:=congrArg Universal233.PaidQueries.Receipt.visits r
 dsimp only [scheduleBits]
 rw [threshold]
 unfold Universal233.PaidQueries.schedule
 split
 · rename_i h
   have nh : ¬decode q<Universal233.PaidQueries.knownCost (js.map (jobValue π ρ))+2*Universal233.PaidQueries.pending (js.map (jobValue π ρ)):=by
    simp only [decide_eq_true_eq] at h;omega
   rw [if_neg nh]
   cases hx : (runBits solve (allocationBits q (knownBits js).value (pendingBits js).value).value js).value.answers with
   | none=>
    apply nativeReceipt_ext
    · simp only [receiptValue,hx,Option.map_none] at aa
      simp [receiptValue,←aa]
    · exact cc
    · exact vv
   | some xs=>
    apply nativeReceipt_ext
    · simp only [receiptValue,hx,Option.map_some] at aa
      simp only [receiptValue,leBits_value,answerBits_value ρ xs,←aa,Option.bind_some]
      split <;> simp_all <;> omega
    · exact cc
    · exact vv
 · rename_i h
   have nh : decode q<Universal233.PaidQueries.knownCost (js.map (jobValue π ρ))+2*Universal233.PaidQueries.pending (js.map (jobValue π ρ)):=by
    simp only [Bool.not_eq_true,decide_eq_false_iff_not] at h;omega
   simp [nh,receiptValue,decode]
end GenericForest.BinaryProducer
