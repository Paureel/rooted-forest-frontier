import GuardedDefs
namespace OrdinaryCommonSplit.Caller
open RMAF Universal233 RestrictionBridge

theorem outside_pair_proper (d : Setup) : DepthOne.proper d.ty d.sy=true := by
  have ny := checked_block_nodup _ _ d.hpT d.Y (by simp)
  have sT : d.Y⊆leaves d.T := fun _ h => (split_labels _ d.X d.Y d.hpT _).2 (Or.inr h)
  have sS : d.Y⊆leaves d.S := fun _ h => (split_labels _ d.X d.Y d.hpS _).2 (Or.inr h)
  have pT := restricted_perm d.T d.ty d.Y d.hty d.nt ny sT
  have pS := restricted_perm d.S d.sy d.Y d.hsy d.ns ny sS
  exact (DepthOne.proper_iff _ _).2 ⟨pT.nodup_iff.2 ny,pS.nodup_iff.2 ny,pT.trans pS.symm⟩

theorem found_one_minimum (T S : Tree) (p : RMAF.Vertex)
    (hp : DepthOne.pretest01 T S=.found (some p)) :
    agreement T S (DepthOne.forest S (some p))=true ∧
    (DepthOne.forest S (some p)).length-1=1 ∧ IsMinimum T S 1 := by
  obtain ⟨a,cost,min⟩ := DepthOne.found_globally_minimum T S (some p) hp
  have one : (DepthOne.forest S (some p)).length-1=1 := by simp [DepthOne.forest]
  exact ⟨a,one,⟨⟨_,a,one⟩,by simpa only [DepthOne.cutCost] using min⟩⟩

/-- Every ANSWER of the actual guarded program is bounded exact under the
child IH only at its actual listed jobs. There is no supplied outside-minimum
premise. Outer refusal remains a separate dispatch applicability obligation. -/
theorem runGuarded_answer_exact (d : Setup) (q : Nat)
    (cb : Tree→Tree→Nat→Option Forest) (answer : Option Forest)
    (ih : GuardedIH d q cb) (h : runGuarded d q cb=some answer) :
    BoundedExact d.T d.S q answer := by
  cases hp : DepthOne.pretest01 d.ty d.sy with
  | refused => simp [runGuarded,hp] at h
  | rejected => simp [runGuarded,hp] at h
  | found c =>
    cases c with
    | none => simp [runGuarded,hp] at h
    | some p =>
      have eq : runWithOutside d q (DepthOne.forest d.sy (some p)) cb=answer := by
        simpa only [runGuarded,hp,Option.some.injEq] using h
      have ih' : ActualIH d q cb := by simpa only [GuardedIH,ActualIH,guardedJobs,hp] using ih
      obtain ⟨a,cost,minimum⟩ := found_one_minimum d.ty d.sy p hp
      rw [←eq]
      exact runWithOutside_exact d q _ cb a cost minimum ih'

theorem runGuarded_nonrefusal_iff (d : Setup) (q : Nat)
    (cb : Tree→Tree→Nat→Option Forest) :
    (∃answer,runGuarded d q cb=some answer) ↔ IsMinimum d.ty d.sy 1 := by
  constructor
  · rintro ⟨answer,h⟩
    cases hp : DepthOne.pretest01 d.ty d.sy with
    | refused => simp [runGuarded,hp] at h
    | rejected => simp [runGuarded,hp] at h
    | found c =>
      cases c with
      | none => simp [runGuarded,hp] at h
      | some p => exact (found_one_minimum d.ty d.sy p hp).2.2
  · intro minimum
    obtain ⟨F,aF,cF⟩ := minimum.1
    obtain ⟨c,hc,ac,cc⟩ := DepthOne.pretest_complete d.ty d.sy (outside_pair_proper d) F aF (by omega)
    cases c with
    | none =>
      have low := minimum.2 _ ac
      simp [DepthOne.forest] at low
    | some p => exact ⟨runWithOutside d q (DepthOne.forest d.sy (some p)) cb,by simp only [runGuarded,hc]⟩

theorem guarded_job_progress (d : Setup) (q : Nat) (j : Job) (hj : j∈guardedJobs d q) :
    DepthOne.proper j.T j.S=true ∧ j.budget<q ∧ q-j.budget=1 := by
  cases hp : DepthOne.pretest01 d.ty d.sy with
  | refused => simp [guardedJobs,hp] at hj
  | rejected => simp [guardedJobs,hp] at hj
  | found c =>
    cases c with
    | none => simp [guardedJobs,hp] at hj
    | some p => exact actual_job_progress d q j (by simpa only [guardedJobs,hp] using hj)

def guardedMass (c : Rat) (d : Setup) (q : Nat) : Rat :=
  ((guardedJobs d q).map (fun j=>c^(-((q-j.budget : Nat) : Int)))).sum

theorem guarded_mass_bound (c : Rat) (hc : 2≤c) (d : Setup) (q : Nat) :
    guardedMass c d q≤1 := by
  cases hp : DepthOne.pretest01 d.ty d.sy with
  | refused => simp [guardedMass,guardedJobs,hp];exact (by decide : (0 : Rat)≤1)
  | rejected => simp [guardedMass,guardedJobs,hp];exact (by decide : (0 : Rat)≤1)
  | found cut =>
    cases cut with
    | none => simp [guardedMass,guardedJobs,hp];exact (by decide : (0 : Rat)≤1)
    | some p => simpa only [guardedMass,guardedJobs,hp,callbackMass] using callback_mass_bound c hc d q
end OrdinaryCommonSplit.Caller

-- deliberate byte corruption
