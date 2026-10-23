import ForwardResidualR3
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair ContactedSource
namespace ContactedForward

/- The only unproved callback contract; actual emitted calls, explicit affordability. -/
def ForwardCallbacks (actual : Tree→Tree→Nat→Option (List (List Nat)))
 {T S : Tree} (s : Rule4.Choice T S) (q : Nat) : Prop :=
 ∀b∈Rule4.branches s,b.cost≤q→Rule4.ExactChild (rule4Child actual) b (q-b.cost)

theorem returned_child_member {T S : Tree} (s : Rule4.Choice T S)
 (actual : Tree→Tree→Nat→Option (List (List Nat))) (q : Nat) {G : (List (List Nat))}
 (member : G∈Rule4.outputs s q (rule4Child actual)) :
 ∃b∈Rule4.branches s,∃affordable : b.cost≤q,rule4Child actual b (q-b.cost)=some G := by
 obtain ⟨b,hb,inChild⟩ := List.mem_flatMap.1 member
 by_cases affordable : b.cost≤q
 · simp only [Rule4.childOutputs,affordable,ite_true] at inChild
   cases ret : rule4Child actual b (q-b.cost) with
   | none => simp only [ret,Option.toList_none] at inChild;cases inChild
   | some H =>
    have eq : G=H := by simpa only [ret,Option.toList_some,List.mem_singleton] using inChild
    subst H;exact ⟨b,hb,affordable,ret⟩
 · simp only [Rule4.childOutputs,affordable,ite_false] at inChild;cases inChild

theorem forward_caller_sound {T S : Tree} (s : Rule4.Choice T S)
 (actual : Tree→Tree→Nat→Option (List (List Nat))) (q : Nat) (callback : ForwardCallbacks actual s q)
 {G : (List (List Nat))} (returned : runRule4 actual s q=some G) :
 agreement T S G=true ∧ G.length-1≤q := by
 have member := (IndependentPaid.best_return List.length (fun _=>true) _ returned).1
 obtain ⟨b,hb,affordable,ret⟩ := returned_child_member s actual q member
 have child := (callback b hb affordable).1 G ret
 exact child_original_budget s hb affordable child.1

theorem forward_caller_complete {T S : Tree} (s : Rule4.Choice T S)
 (actual : Tree→Tree→Nat→Option (List (List Nat))) (q : Nat) (callback : ForwardCallbacks actual s q)
 (F : (List (List Nat))) (hF : agreement T S F=true) (budget : F.length-1≤q) :
 ∃G,runRule4 actual s q=some G ∧ G.length≤F.length := by
 obtain ⟨b,hb,H,covered,len⟩ := actual_forward_coverage s F hF
 have hBudget : H.length-1≤q := by omega
 have feasible := original_affordable_child s hb covered hBudget
 obtain ⟨G,hG,glen⟩ := (callback b hb feasible.1).2 H feasible.2
 have member : G∈Rule4.outputs s q (rule4Child actual) := by
  apply List.mem_flatMap.2
  refine ⟨b,hb,?_⟩
  simp only [Rule4.childOutputs,feasible.1,ite_true,hG,Option.toList_some,List.mem_singleton]
 obtain ⟨B,hB,least⟩ := IndependentPaid.best_witness List.length (fun _=>true) _ member rfl
 exact ⟨B,hB,Nat.le_trans least (Nat.le_trans glen len)⟩

theorem checked_forward_caller (actual : Tree→Tree→Nat→Option (List (List Nat))) (q : Nat)
 {T S : Tree} (s : Rule4.Choice T S)
 (_proper : DepthOne.proper T S=true) (_rejected : DepthOne.pretest01 T S=.rejected)
 (_selected : early T S=.rule4Forward s) (callback : ForwardCallbacks actual s q) :
 QueryExact T S q (runRule4 actual s q) := by
 cases returned : runRule4 actual s q with
 | none =>
  intro F hF
  by_cases budget : F.length-1≤q
  · obtain ⟨G,hG,_⟩ := forward_caller_complete s actual q callback F hF budget
    rw [returned] at hG;cases hG
  · omega
 | some G =>
  have sound := forward_caller_sound s actual q callback returned
  refine ⟨sound.1,sound.2,?_⟩
  intro F hF
  by_cases budget : F.length-1≤q
  · obtain ⟨B,hB,least⟩ := forward_caller_complete s actual q callback F hF budget
    have eq : B=G := Option.some.inj (hB.symm.trans returned)
    exact eq ▸ least
  · omega

end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.returned_child_member
#print axioms ContactedForward.returned_child_member
#check @ContactedForward.forward_caller_sound
#print axioms ContactedForward.forward_caller_sound
#check @ContactedForward.forward_caller_complete
#print axioms ContactedForward.forward_caller_complete
#check @ContactedForward.checked_forward_caller
#print axioms ContactedForward.checked_forward_caller
