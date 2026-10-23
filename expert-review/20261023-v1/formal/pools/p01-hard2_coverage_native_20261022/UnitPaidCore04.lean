import FastSolve
import Hard2Combine
import CommonDispatch
import Endpoint
import Endpoints
namespace UnitPaidCombination
open RMAF Universal233 Universal233.CherryBranching Universal233.BothBad OrdinaryDispatch

def Cohabit (a b : Nat) (F : OrdinaryDispatch.Forest) : Prop := ∃ B, B∈F ∧ a∈B ∧ b∈B

/-- The paid execution is tied to this original input, selected candidate and
budget. Completeness is required only for cohabiting original AF competitors. -/
structure CohabitingPaidCover (T S : Tree) (c : Candidate) (q : Nat)
    (paid : Execution) : Prop where
 sound : ∀ G, paid.answer=some G → agreement T S G=true ∧ G.length-1≤q
 cover : ∀ F, agreement T S F=true → F.length-1≤q → Cohabit c.a c.b F →
   ∃ G, paid.answer=some G ∧ G.length≤F.length

def Below (q : Nat) (actual : Hard2Combine.Ordinary) : Prop :=
 ∀ r, r<q → ∀ T S, DepthOne.proper T S=true → QueryExact T S r (actual T S r)

theorem choose_sound (a b : Option OrdinaryDispatch.Forest) (P : OrdinaryDispatch.Forest→Prop)
    (ha : ∀ F,a=some F→P F) (hb : ∀ F,b=some F→P F) :
    ∀ F, choose a b=some F → P F := by
 intro F h
 cases a with
 | none => exact hb F (by simpa [choose] using h)
 | some A =>
  cases b with
  | none => exact ha F (by simpa [choose] using h)
  | some B =>
   by_cases ab : A.length≤B.length
   · exact ha F (by simpa [choose,ab] using h)
   · exact hb F (by simpa [choose,ab] using h)

theorem choose_left_le (A : OrdinaryDispatch.Forest) (b : Option OrdinaryDispatch.Forest) :
    ∃ H, choose (some A) b=some H ∧ H.length≤A.length := by
 cases b with
 | none => exact ⟨A,by simp [choose]⟩
 | some B =>
  by_cases ab : A.length≤B.length
  · exact ⟨A,by simp [choose,ab]⟩
  · exact ⟨B,by simp [choose,ab];omega⟩

theorem choose_right_le (a : Option OrdinaryDispatch.Forest) (B : OrdinaryDispatch.Forest) :
    ∃ H, choose a (some B)=some H ∧ H.length≤B.length := by
 cases a with
 | none => exact ⟨B,by simp [choose]⟩
 | some A =>
  by_cases ab : A.length≤B.length
  · exact ⟨A,by simp [choose,ab]⟩
  · exact ⟨B,by simp [choose,ab]⟩

theorem choose_first_tie (A B : OrdinaryDispatch.Forest) (h : A.length=B.length) :
    choose (some A) (some B)=some A := by simp [choose,h]

theorem checked_sound (T S : Tree) (q : Nat) (raw : Option OrdinaryDispatch.Forest) (F : OrdinaryDispatch.Forest)
    (h : checked T S q raw=some F) : agreement T S F=true ∧ F.length-1≤q := by
 cases raw with
 | none => simp [checked] at h
 | some G =>
  by_cases good : accept T S q G=true
  · have eq : G=F := by simpa [checked,good] using h
    subst F
    simpa only [accept,Bool.and_eq_true,decide_eq_true_eq] using good
  · simp [checked,good] at h

theorem unit_calls_zero (T S : Tree) (a b : Nat) :
    Hard2Combine.unitCalls S T a b 0=[] := by
 simp [Hard2Combine.unitCalls,remaining,singletonChild,makeChild]

theorem unit_calls_positive (T S : Tree) (a b q : Nat) (hq : 1≤q) :
    Hard2Combine.unitCalls S T a b q=
      [⟨some T,(singletonChild S a).sourceForest,q-1⟩,
       ⟨some T,(singletonChild S b).sourceForest,q-1⟩] := by
 simp [Hard2Combine.unitCalls,remaining,singletonChild,makeChild,hq]

theorem unit_calls_strict (T S : Tree) (a b q : Nat)
    (call : Call) (h : call∈Hard2Combine.unitCalls S T a b q) : call.budget<q := by
 by_cases hq : 1≤q
 · rw [unit_calls_positive T S a b q hq] at h
   simp only [List.mem_cons,List.not_mem_nil,or_false] at h
   rcases h with rfl|rfl <;> simp only <;> omega
 · have zero : q=0 := by omega
   subst q
   rw [unit_calls_zero] at h
   exact False.elim (List.not_mem_nil h)

theorem literal_call_order (actual : Hard2Combine.Ordinary) (T S : Tree)
    (a b q : Nat) (paid : Execution) :
    (Hard2Combine.combine actual T S a b q paid).calls=
      Hard2Combine.unitCalls S T a b q++paid.calls := rfl

/-- Internal algebra only. The final theorem discharges both unit hypotheses. -/
theorem combine_of_unit_cover (actual : Hard2Combine.Ordinary) (T S : Tree)
    (c : Candidate) (q : Nat) (paid : Execution)
    (unitSound : ∀ G,runChildren actual T S q [singletonChild S c.a,singletonChild S c.b]=some G →
      agreement T S G=true ∧ G.length-1≤q)
    (unitCover : ∀ F,agreement T S F=true → F.length-1≤q → ¬Cohabit c.a c.b F →
      ∃ G,runChildren actual T S q [singletonChild S c.a,singletonChild S c.b]=some G ∧ G.length≤F.length)
    (paidCover : CohabitingPaidCover T S c q paid) :
    QueryExact T S q (Hard2Combine.combine actual T S c.a c.b q paid).answer := by
 classical
 let units:=runChildren actual T S q [singletonChild S c.a,singletonChild S c.b]
 have sound : ∀ H,choose units paid.answer=some H → agreement T S H=true ∧ H.length-1≤q :=
   choose_sound units paid.answer _ unitSound paidCover.sound
 have cover : ∀ F,agreement T S F=true → F.length-1≤q →
     ∃ H,choose units paid.answer=some H ∧ H.length≤F.length := by
  intro F hF budget
  by_cases hc : Cohabit c.a c.b F
  · obtain ⟨G,hG,le⟩:=paidCover.cover F hF budget hc
    obtain ⟨H,hH,leH⟩:=choose_right_le units G
    exact ⟨H,by simpa [hG] using hH,Nat.le_trans leH le⟩
  · obtain ⟨G,hG,le⟩:=unitCover F hF budget hc
    obtain ⟨H,hH,leH⟩:=choose_left_le G paid.answer
    exact ⟨H,by simpa [units,hG] using hH,Nat.le_trans leH le⟩
 change QueryExact T S q (choose units paid.answer)
 cases answer : choose units paid.answer with
 | none =>
  intro F hF
  by_cases budget : F.length-1≤q
  · obtain ⟨H,hH,_⟩:=cover F hF budget
    simp [answer] at hH
  · omega
 | some H =>
  have hs:=sound H answer
  refine ⟨hs.1,hs.2,?_⟩
  intro F hF
  by_cases budget : F.length-1≤q
  · obtain ⟨G,hG,le⟩:=cover F hF budget
    have eq : H=G := Option.some.inj (answer.symm.trans hG)
    simpa [eq] using le
  · have hb:=hs.2
    omega
end UnitPaidCombination

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @UnitPaidCombination.choose_sound
#print axioms UnitPaidCombination.choose_sound
#check @UnitPaidCombination.choose_left_le
#print axioms UnitPaidCombination.choose_left_le
#check @UnitPaidCombination.choose_right_le
#print axioms UnitPaidCombination.choose_right_le
#check @UnitPaidCombination.choose_first_tie
#print axioms UnitPaidCombination.choose_first_tie
#check @UnitPaidCombination.checked_sound
#print axioms UnitPaidCombination.checked_sound
#check @UnitPaidCombination.unit_calls_zero
#print axioms UnitPaidCombination.unit_calls_zero
#check @UnitPaidCombination.unit_calls_positive
#print axioms UnitPaidCombination.unit_calls_positive
#check @UnitPaidCombination.unit_calls_strict
#print axioms UnitPaidCombination.unit_calls_strict
#check @UnitPaidCombination.literal_call_order
#print axioms UnitPaidCombination.literal_call_order
#check @UnitPaidCombination.combine_of_unit_cover
#print axioms UnitPaidCombination.combine_of_unit_cover
