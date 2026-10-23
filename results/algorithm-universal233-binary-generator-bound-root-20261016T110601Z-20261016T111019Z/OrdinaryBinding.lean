import CommonConsumer
import ForestMinimumCompletion
namespace Universal233.Rule5CommonOrdinary
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification Rule5FinalClassification Rule5CommonSelector

/-- The actual selected source call at the current cut budget, flattened once.
No callback replacement or mathematical completion occurs in this body. -/
def runSelectedCommon (actual : Tree→Tree→Nat→Option (List (List Nat)))
 (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) : Option (List (List Nat)) :=
 (runCommon T S a b d q actual).join

theorem local_callback_bounded (actual : Tree→Tree→Nat→Option (List (List Nat)))
 (r : Nat) (ih : ForestMinCompletion.LocalOrdinaryIH r actual) (T S : Tree)
 (proper : DepthOne.proper T S=true) :
 OrdinaryCommonSplit.Caller.BoundedExact T S r (actual T S r) := by
 cases answer : actual T S r with
 | none =>
   intro G hG
   apply Nat.lt_of_not_ge
   intro budget
   obtain ⟨F,hF⟩ := ih.complete T S r G (Nat.le_refl _) proper hG budget
   rw [answer] at hF
   contradiction
 | some F =>
   have hs := ih.sound T S r F (Nat.le_refl _) proper answer
   exact ⟨hs.1,hs.2.1,fun G hG => Nat.sub_le_sub_right (hs.2.2 G hG) 1⟩

theorem callback_jobs_below (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat)
 (j : OrdinaryCommonSplit.Caller.Job) (hj : j∈commonJobs T S a b d q) :
 DepthOne.proper j.T j.S=true ∧ j.budget<q ∧ q-j.budget=1 :=
 selected_one_job_progress T S a b d q j hj

theorem actual_source_ih (actual : Tree→Tree→Nat→Option (List (List Nat)))
 (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat)
 (smaller : ∀r,r<q → ForestMinCompletion.LocalOrdinaryIH r actual) :
 OrdinaryCommonSplit.Source.SourceIH T S (subtreeLabels S d.badArc)
   (outsideLabels S a b d) d.badArc q actual := by
 intro j hj
 have prog := callback_jobs_below T S a b d q j hj
 exact local_callback_bounded actual j.budget (smaller j.budget prog.2.1) j.T j.S prog.1

theorem selected_bounded {T S : Tree} {i edge : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : selectFinal T S a b=some (.remaining d (.one edge)))
 (actual : Tree→Tree→Nat→Option (List (List Nat))) (q : Nat)
 (smaller : ∀r,r<q → ForestMinCompletion.LocalOrdinaryIH r actual) :
 OrdinaryCommonSplit.Caller.BoundedExact T S q (runSelectedCommon actual T S a b d q) := by
 obtain ⟨answer,run,exactness⟩ := selected_one_bounded_solver ch ad sel q actual
   (actual_source_ih actual T S a b d q smaller)
 simpa only [runSelectedCommon,run,Option.join_some] using exactness

theorem original_forest_length_positive {T S : Tree} {F : List (List Nat)}
 (ha : agreement T S F=true) : 0<F.length := by
 have pos := leaves_length_positive T
 have nonempty : leaves T≠[] := by intro eq; simp [eq] at pos
 obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil (leaves T) nonempty
 obtain ⟨B,hB,_⟩ := partitionCheck_covers (leaves T) F (BinaryExchange.agreement_parts T S F ha).1 x hx
 apply List.length_pos_iff.2
 intro eq
 simp [eq] at hB

theorem bounded_some_minimum {T S : Tree} {q : Nat} {F : List (List Nat)}
 (ex : OrdinaryCommonSplit.Caller.BoundedExact T S q (some F)) :
 agreement T S F=true ∧ F.length-1≤q ∧ ∀G,agreement T S G=true → F.length≤G.length := by
 refine ⟨ex.1,ex.2.1,?_⟩
 intro G hG
 have fpos := original_forest_length_positive ex.1
 have gpos := original_forest_length_positive hG
 have least := ex.2.2 G hG
 omega

theorem selected_sound_minimum {T S : Tree} {i edge : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : selectFinal T S a b=some (.remaining d (.one edge)))
 (actual : Tree→Tree→Nat→Option (List (List Nat))) (q : Nat)
 (smaller : ∀r,r<q → ForestMinCompletion.LocalOrdinaryIH r actual)
 {F : List (List Nat)} (answer : runSelectedCommon actual T S a b d q=some F) :
 agreement T S F=true ∧ F.length-1≤q ∧ ∀G,agreement T S G=true → F.length≤G.length := by
 have ex := selected_bounded ch ad sel actual q smaller
 rw [answer] at ex
 exact bounded_some_minimum ex

theorem selected_complete {T S : Tree} {i edge : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : selectFinal T S a b=some (.remaining d (.one edge)))
 (actual : Tree→Tree→Nat→Option (List (List Nat))) (q : Nat)
 (smaller : ∀r,r<q → ForestMinCompletion.LocalOrdinaryIH r actual)
 (G : List (List Nat)) (ha : agreement T S G=true) (budget : G.length-1≤q) :
 ∃F,runSelectedCommon actual T S a b d q=some F ∧ F.length≤G.length := by
 have ex := selected_bounded ch ad sel actual q smaller
 cases out : runSelectedCommon actual T S a b d q with
 | none =>
   rw [out] at ex
   have no := ex G ha
   omega
 | some F =>
   rw [out] at ex
   exact ⟨F,rfl,(bounded_some_minimum ex).2.2 G ha⟩

theorem selected_none_iff {T S : Tree} {i edge : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : selectFinal T S a b=some (.remaining d (.one edge)))
 (actual : Tree→Tree→Nat→Option (List (List Nat))) (q : Nat)
 (smaller : ∀r,r<q → ForestMinCompletion.LocalOrdinaryIH r actual) :
 runSelectedCommon actual T S a b d q=none ↔ ∀G,agreement T S G=true → q<G.length-1 := by
 constructor
 · intro out
   have ex := selected_bounded ch ad sel actual q smaller
   rw [out] at ex
   exact ex
 · intro no
   cases out : runSelectedCommon actual T S a b d q with
   | none => rfl
   | some F =>
     have hs := selected_sound_minimum ch ad sel actual q smaller out
     have low := no F hs.1
     omega
end Universal233.Rule5CommonOrdinary
