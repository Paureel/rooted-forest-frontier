import QueryMass

namespace Universal233.PaidQueries

structure MeterReceipt (P A : Type) where
  value : Receipt A
  queries : List (P × Nat)
  callerWork : Nat
  recursiveWork : Nat

/- Declared conservative unit source model: one list/constructor/projection/
   Option/branch operation or bounded-word Nat operation costs at most one.
   Hard call dispatch, returned payload and trace cons use8 units, resolved
   dispatch/Option map/answer cons use5; nil uses2. The recursive call's supplied
   charge is evaluated at the EXACT problem and budget of the actual dispatch.
   These contracts require source review; no extracted instruction identity. -/
def meterRun (solve : P → Nat → Option (Nat × A)) (charge : P → Nat → Nat)
    (b : Nat) : List (Job P A) → MeterReceipt P A
  | [] => ⟨⟨some [],[],0⟩,[],2,0⟩
  | .resolved _ c a :: js =>
    let r := meterRun solve charge b js
    ⟨⟨r.value.answers.map ((c,a)::·),r.value.calls,r.value.visits+1⟩,
      r.queries,r.callerWork+5,r.recursiveWork⟩
  | .hard p :: js =>
    match solve p b with
    | none => ⟨⟨none,[b],1⟩,[(p,b)],8,charge p b⟩
    | some x =>
      let r := meterRun solve charge b js
      ⟨⟨r.value.answers.map (x::·),b::r.value.calls,r.value.visits+1⟩,
        (p,b)::r.queries,r.callerWork+8,charge p b+r.recursiveWork⟩

theorem meterRun_value (solve : P → Nat → Option (Nat × A)) (charge : P → Nat → Nat)
    (b : Nat) (js : List (Job P A)) : (meterRun solve charge b js).value=run solve b js := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    cases j with
    | resolved p c a => simp only [meterRun,run,ih]
    | hard p => cases he : solve p b <;> simp only [meterRun,run,he,ih]

theorem meterRun_trace (solve : P → Nat → Option (Nat × A)) (charge : P → Nat → Nat)
    (b : Nat) (js : List (Job P A)) :
    (meterRun solve charge b js).queries.map Prod.snd = (run solve b js).calls ∧
      (meterRun solve charge b js).recursiveWork =
        ((meterRun solve charge b js).queries.map (fun pb => charge pb.1 pb.2)).sum := by
  induction js with
  | nil => simp [meterRun,run]
  | cons j js ih =>
    cases j with
    | resolved p c a => simpa [meterRun,run] using ih
    | hard p =>
      cases he : solve p b with
      | none => simp [meterRun,run,he]
      | some x => simpa [meterRun,run,he] using ih

theorem meterRun_caller (solve : P → Nat → Option (Nat × A)) (charge : P → Nat → Nat)
    (b : Nat) (js : List (Job P A)) :
    (meterRun solve charge b js).callerWork ≤ 8*js.length+2 := by
  induction js with
  | nil => simp [meterRun]
  | cons j js ih =>
    cases j with
    | resolved p c a => simp only [meterRun,List.length_cons]; omega
    | hard p => cases he : solve p b <;> simp only [meterRun,he,List.length_cons] <;> omega

def postCharge (r : Receipt A) : Nat := match r.answers with
  | none => 4
  | some xs => 4*xs.length+4

/- Two preprocessing scans for the lower bill, then at most two more for the
   allocated budget; returned answer map+sum and final comparison are charged.
   q and cost bit lengths must be included when Nat operations are not unit. -/
def meterSchedule (solve : P → Nat → Option (Nat × A)) (charge : P → Nat → Nat)
    (q : Nat) (js : List (Job P A)) : MeterReceipt P A :=
  if q < knownCost js + 2*pending js then
    ⟨⟨none,[],0⟩,[],8*js.length+8,0⟩ else
    let r := meterRun solve charge (allocated q js) js
    ⟨⟨r.value.answers.bind (fun xs => if answerCost xs ≤ q then some xs else none),
        r.value.calls,r.value.visits⟩,r.queries,
      16*js.length+20+r.callerWork+postCharge r.value,r.recursiveWork⟩

theorem meterSchedule_value (solve : P → Nat → Option (Nat × A)) (charge : P → Nat → Nat)
    (q : Nat) (js : List (Job P A)) :
    (meterSchedule solve charge q js).value = schedule solve q js := by
  unfold meterSchedule schedule
  split
  · rfl
  · simp only [meterRun_value]

theorem run_answer_length (solve : P → Nat → Option (Nat × A)) (b : Nat)
    (js : List (Job P A)) (xs : List (Nat × A))
    (h : (run solve b js).answers = some xs) : xs.length=js.length := by
  induction js generalizing xs with
  | nil => have he : xs=[] := by simpa [run] using h.symm
           simp [he]
  | cons j js ih =>
    cases j with
    | resolved p c a =>
      cases he : (run solve b js).answers with
      | none => simp [run,he] at h
      | some ys =>
        have hx : xs=(c,a)::ys := by simpa [run,he] using h.symm
        simp [hx,ih ys he]
    | hard p =>
      cases he : solve p b with
      | none => simp [run,he] at h
      | some x =>
        cases ht : (run solve b js).answers with
        | none => simp [run,he,ht] at h
        | some ys =>
          have hx : xs=x::ys := by simpa [run,he,ht] using h.symm
          simp [hx,ih ys ht]

theorem meterSchedule_caller (solve : P → Nat → Option (Nat × A)) (charge : P → Nat → Nat)
    (q : Nat) (js : List (Job P A)) :
    (meterSchedule solve charge q js).callerWork ≤ 32*(js.length+1) := by
  unfold meterSchedule
  split
  · simp only []; omega
  · have hm := meterRun_caller solve charge (allocated q js) js
    have hp : postCharge (meterRun solve charge (allocated q js) js).value ≤ 4*js.length+4 := by
      rw [meterRun_value]
      cases he : (run solve (allocated q js) js).answers with
      | none => simp [postCharge,he]
      | some xs => simp [postCharge,he,run_answer_length solve (allocated q js) js xs he]
    simp only []
    omega

theorem meterSchedule_trace (solve : P → Nat → Option (Nat × A)) (charge : P → Nat → Nat)
    (q : Nat) (js : List (Job P A)) :
    (meterSchedule solve charge q js).queries.map Prod.snd = (schedule solve q js).calls ∧
      (meterSchedule solve charge q js).recursiveWork =
        ((meterSchedule solve charge q js).queries.map (fun pb => charge pb.1 pb.2)).sum := by
  unfold meterSchedule schedule
  split
  · simp
  · have ht := meterRun_trace solve charge (allocated q js) js
    simpa only [meterRun_value] using ht
end Universal233.PaidQueries
