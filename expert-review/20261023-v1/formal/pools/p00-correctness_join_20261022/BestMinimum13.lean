-- Own proof of the actual best recursion, no author minimum theorem.
import CommonDispatch
import PaidChildren
open RMAF OrdinaryDispatch
namespace HighCompletion
def MinimumSpec {α : Type} (cost : α→Nat) (valid : α→Bool) (xs : List α) : Option α→Prop
 | none => ∀x∈xs,valid x=false
 | some F => F∈xs ∧ valid F=true ∧ ∀G∈xs,valid G=true → cost F≤cost G
theorem best_minimum {α : Type} (cost : α→Nat) (valid : α→Bool) (xs : List α) :
    MinimumSpec cost valid xs (best cost valid xs) := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons a xs ih =>
    rw [best.eq_2]
    by_cases hv : valid a=true
    · rw [if_pos hv]
      cases hb : best cost valid xs with
      | none =>
        rw [hb] at ih
        refine ⟨List.mem_cons_self,hv,?_⟩
        intro G hG hvalid
        rcases List.mem_cons.mp hG with rfl | hG
        · exact Nat.le_refl _
        · exact False.elim (Bool.noConfusion ((ih G hG).symm.trans hvalid))
      | some b =>
        rw [hb] at ih
        dsimp only
        by_cases hc : cost a≤cost b
        · rw [if_pos hc]
          refine ⟨List.mem_cons_self,hv,?_⟩
          intro G hG hvalid
          rcases List.mem_cons.mp hG with rfl | hG
          · exact Nat.le_refl _
          · exact Nat.le_trans hc (ih.2.2 G hG hvalid)
        · rw [if_neg hc]
          refine ⟨List.mem_cons_of_mem a ih.1,ih.2.1,?_⟩
          intro G hG hvalid
          rcases List.mem_cons.mp hG with rfl | hG
          · exact Nat.le_of_lt (Nat.lt_of_not_ge hc)
          · exact ih.2.2 G hG hvalid
    · rw [if_neg hv]
      cases hb : best cost valid xs with
      | none =>
        rw [hb] at ih
        intro G hG
        rcases List.mem_cons.mp hG with rfl | hG
        · exact Bool.eq_false_iff.mpr hv
        · exact ih G hG
      | some b =>
        rw [hb] at ih
        refine ⟨List.mem_cons_of_mem a ih.1,ih.2.1,?_⟩
        intro G hG hvalid
        rcases List.mem_cons.mp hG with rfl | hG
        · exact False.elim (hv hvalid)
        · exact ih.2.2 G hG hvalid
def AnswersComplete (T S : Tree) (q : Nat) (answers : List (List (List Nat))) : Prop :=
 ∀G,agreement T S G=true → G.length-1≤q →
   ∃F∈answers,ordinaryAccepted T S q F=true ∧ F.length≤G.length
theorem query_exact_of_answers_complete (T S : Tree) (q : Nat)
    (answers : List (List (List Nat))) (hcomp : AnswersComplete T S q answers) :
    QueryExact T S q (best List.length (ordinaryAccepted T S q) answers) := by
  have hb:=best_minimum List.length (ordinaryAccepted T S q) answers
  cases hout : best List.length (ordinaryAccepted T S q) answers with
  | none =>
    rw [hout] at hb
    intro G hag
    apply Nat.lt_of_not_ge
    intro hcost
    obtain ⟨F,hF,hvalid,_⟩:=hcomp G hag hcost
    exact Bool.noConfusion ((hb F hF).symm.trans hvalid)
  | some F =>
    rw [hout] at hb
    have haccept:=hb.2.1
    simp only [ordinaryAccepted,Bool.and_eq_true,decide_eq_true_eq] at haccept
    refine ⟨haccept.1,haccept.2,?_⟩
    intro G hag
    by_cases hcost : G.length-1≤q
    · obtain ⟨H,hH,hvalid,hlen⟩:=hcomp G hag hcost
      exact Nat.le_trans (hb.2.2 H hH hvalid) hlen
    · have hFcost:=haccept.2
      omega
#print axioms best_minimum
#print axioms query_exact_of_answers_complete
end HighCompletion
