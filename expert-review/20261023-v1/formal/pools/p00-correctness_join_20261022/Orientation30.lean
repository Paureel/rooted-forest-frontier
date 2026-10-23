-- Own source-target symmetry from original agreement definitions.
import ConsumerGeometry32
import CallbackConsumer23
open RMAF OrdinaryDispatch FastOrdinary
namespace HighCompletion
theorem same_shape_swap (T S : Tree) : sameShape T S=sameShape S T := by
  induction T generalizing S with
  | leaf a =>
    cases S with
    | leaf b =>
      simp only [sameShape.eq_1]
      by_cases h : a=b
      · subst b; rfl
      · have h1 : (a==b)=false := Bool.eq_false_iff.mpr (fun he=>h (beq_iff_eq.mp he))
        have h2 : (b==a)=false := Bool.eq_false_iff.mpr (fun he=>h (beq_iff_eq.mp he).symm)
        rw [h1,h2]
    | node L R => rfl
  | node L R ihL ihR =>
    cases S with
    | leaf b => rfl
    | node X Y =>
      rw [sameShape.eq_2,sameShape.eq_2,ihL X,ihL Y,ihR X,ihR Y]
      ac_rfl
theorem restriction_agrees_swap (T S : Tree) (B : List Nat) :
    restrictionAgrees T S B=restrictionAgrees S T B := by
  unfold restrictionAgrees
  cases ht : restrict B T <;> cases hs : restrict B S
  · rfl
  · rfl
  · rfl
  · exact same_shape_swap _ _
theorem agreement_swap (T S : Tree) (F : List (List Nat)) :
    agreement T S F=agreement S T F := by
  have hr : F.all (restrictionAgrees T S)=F.all (restrictionAgrees S T) := by
    apply congrArg (fun p=>F.all p)
    funext B
    exact restriction_agrees_swap T S B
  unfold agreement
  rw [hr]
  ac_rfl
theorem agreement_oriented (T S : Tree) (reverse : Bool) (F : List (List Nat)) :
    agreement (Oriented reverse T S).1 (Oriented reverse T S).2 F=agreement T S F := by
  cases reverse
  · rfl
  · exact agreement_swap S T F
theorem query_exact_oriented (T S : Tree) (reverse : Bool) (q : Nat)
    (result : Option (List (List Nat))) :
    QueryExact (Oriented reverse T S).1 (Oriented reverse T S).2 q result ↔ QueryExact T S q result := by
  cases result with
  | none => simp only [QueryExact,agreement_oriented]
  | some F => simp only [QueryExact,agreement_oriented]
end HighCompletion
