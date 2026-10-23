import MafCaller

namespace Universal233.MafScheduler
open RMAF PaidQueries RestrictionBridge

def LocalMinimum (t s : Tree) (m : Nat) : Prop :=
  (∃ F, agreement t s F=true ∧ F.length-1=m) ∧
    ∀ F, agreement t s F=true → m≤F.length-1

def LocalValid (t s : List Nat → Tree) (m : List Nat → Nat)
    (U : List Nat) (F : Forest) : Prop := agreement (t U) (s U) F=true ∧ F.length-1=m U

theorem local_slot (T S : Tree) (t s : List Nat → Tree) (m : List Nat → Nat)
    (U : List Nat) (hb : properBlock T S U=true)
    (ht : restrict U T=some (t U)) (hs : restrict U S=some (s U))
    (hp : DepthOne.proper (t U) (s U)=true) (hm : LocalMinimum (t U) (s U) (m U)) :
    ∃ j, slot T S U=some j ∧ j.problem=U ∧ Planned m (LocalValid t s m) j := by
  cases he : DepthOne.pretest01 (t U) (s U) with
  | refused =>
    have hf := (DepthOne.refused_iff (t U) (s U)).1 he
    simp [hp] at hf
  | rejected =>
    refine ⟨.hard U,by simp [slot,hb,ht,hs,he],rfl,?_⟩
    obtain ⟨F,hF,hcost⟩ := hm.1
    have hl := DepthOne.rejected_lower_bound (t U) (s U) he F hF
    simpa [Planned,←hcost] using hl
  | found c =>
    obtain ⟨ha,hcost,hmin⟩ := DepthOne.found_globally_minimum (t U) (s U) c he
    obtain ⟨F,hF,hopt⟩ := hm.1
    have hl := hmin F hF
    have hu := hm.2 _ ha
    have heq : DepthOne.cutCost c=m U := by omega
    refine ⟨.resolved U (DepthOne.cutCost c) (DepthOne.forest (s U) c),
      by simp [slot,hb,ht,hs,he],rfl,heq,?_,DepthOne.cutCost_le_one c⟩
    exact ⟨ha,by omega⟩

theorem checked_block_proper (T S : Tree) (Q : Forest)
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q=true) (hQS : partitionCheck (leaves S) Q=true)
    (t s : List Nat → Tree)
    (ht : ∀ U∈Q, restrict U T=some (t U)) (hs : ∀ U∈Q, restrict U S=some (s U)) :
    ∀ U∈Q, properBlock T S U=true ∧ DepthOne.proper (t U) (s U)=true := by
  intro U hU
  have hnd := checked_block_nodup (leaves T) Q hQT U hU
  have hne := checked_nonempty (leaves T) Q hQT U hU
  have hb : properBlock T S U=true := by
    simp only [properBlock,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.all_eq_true]
    refine ⟨⟨hnd,?_⟩,?_⟩
    · cases U <;> simp_all
    · intro x hx
      simp only [Bool.and_eq_true,List.contains_iff_mem]
      exact ⟨checked_label (leaves T) Q hQT hU hx,checked_label (leaves S) Q hQS hU hx⟩
  have lt := component_labels T (t U) U Q (ht U hU) pt hQT hU
  have ls := component_labels S (s U) U Q (hs U hU) ps hQS hU
  refine ⟨hb,(DepthOne.proper_iff _ _).2 ⟨?_,?_,lt.trans ls.symm⟩⟩
  · exact restricted_nodup T (t U) U (ht U hU) pt
  · exact restricted_nodup S (s U) U (hs U hU) ps

theorem prepare_planned (T S : Tree) (Q : Forest) (t s : List Nat → Tree) (m : List Nat → Nat)
    (ht : ∀ U∈Q, restrict U T=some (t U)) (hs : ∀ U∈Q, restrict U S=some (s U))
    (hp : ∀ U∈Q, properBlock T S U=true ∧ DepthOne.proper (t U) (s U)=true)
    (hm : ∀ U∈Q, LocalMinimum (t U) (s U) (m U)) :
    ∃ js, prepare T S Q=some js ∧ js.map Job.problem=Q ∧
      ∀ j∈js, Planned m (LocalValid t s m) j := by
  induction Q with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | cons U Q ih =>
    obtain ⟨j,hj,hkey,hplan⟩ := local_slot T S t s m U (hp U (by simp)).1
      (ht U (by simp)) (hs U (by simp)) (hp U (by simp)).2 (hm U (by simp))
    obtain ⟨js,hjs,hkeys,hplans⟩ := ih
      (fun V hv => ht V (by simp [hv])) (fun V hv => hs V (by simp [hv]))
      (fun V hv => hp V (by simp [hv])) (fun V hv => hm V (by simp [hv]))
    refine ⟨j::js,by simp [prepare,hj,hjs],by simp [hkey,hkeys],?_⟩
    intro k hk
    rcases List.mem_cons.1 hk with he | he
    · simpa [he] using hplan
    · exact hplans k he
end Universal233.MafScheduler
