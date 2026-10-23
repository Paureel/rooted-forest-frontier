import ActualCandidates
namespace GenericForest.CheckCorrespondence
open RMAF ForestState RestrictionBridge Universal233 SourceCoverage WholeSourceWork CoreWork FrontierWork PaidQueries

/-- The proper-input guard is bounded even when it rejects malformed inputs. -/
theorem proper_work_le_inspection (T : Option Tree) (ss : List Tree) (q : Nat) :
 (meterProper T ss).work≤inspectionBill T ss q := by
 let N:=targetNodes T+sourceNodes ss+ss.length+q
 have h:=meterProper_cap T ss N (by dsimp [N];omega) (by dsimp [N];omega) (by dsimp [N];omega)
 have bound:=cap_lift N 164 3 8 _ h (by decide)
 exact Nat.le_trans bound (Nat.mul_le_mul_right ((N+1)^8) (by decide : 164≤4096))

theorem initial_check_bound (T : Option Tree) (ss : List Tree) (q : Nat)
 (proper : ForestState.proper T ss=true) :
 (meterAgrees T ss (ss.map leaves)).work≤inspectionBill T ss q :=
 agrees_work_le_inspection _ _ _ _ (state_payload_source T ss proper)

theorem actual_singleton_check_bound (actual : Ordinary) (bound : ReturnedPayloadBound actual)
 (t s : Tree) (q : Nat) (F : Forest) (proper : ForestState.proper (some t) [s]=true)
 (answer : actual t s q=some F) :
 (meterChecked (some t) [s] q F).work≤inspectionBill (some t) [s] q :=
 checked_work_le_inspection _ _ _ _
   (state_payload_ordinary_return actual bound t s q F (singleton_ordinary_proper t s proper) answer)

theorem actual_scheduled_check_bound (actual : Ordinary) (bound : ReturnedPayloadBound actual)
 (t : Tree) (ss : List Tree) (q : Nat) (proper : ForestState.proper (some t) ss=true)
 (js : List (Job (Tree×Tree) Forest)) (hjobs : jobs t ss=some js) (xs : List (Nat×Forest))
 (answer : (schedule (fun p b=>(actual p.1 p.2 b).map (fun F=>(F.length-1,F))) q js).answers=some xs) :
 (meterChecked (some t) ss q (xs.flatMap Prod.snd)).work≤inspectionBill (some t) ss q :=
 checked_work_le_inspection _ _ _ _ (scheduled_payload actual bound t ss q proper js hjobs xs answer)

theorem disjoint_attempt_check_bound (actual : Ordinary) (bound : ReturnedPayloadBound actual)
 (t : Tree) (ss : List Tree) (q : Nat) (proper : ForestState.proper (some t) ss=true)
 (r : PaidQueries.Receipt Forest) (attempt : disjointAttempt t ss actual q=some r)
 (xs : List (Nat×Forest)) (answer : r.answers=some xs) :
 (meterChecked (some t) ss q (xs.flatMap Prod.snd)).work≤inspectionBill (some t) ss q := by
 unfold disjointAttempt at attempt
 cases hj : jobs t ss with
 | none=>simp [hj] at attempt
 | some js=>
  have eq : r=schedule (fun p b=>(actual p.1 p.2 b).map (fun F=>(F.length-1,F))) q js:=by
   simpa [hj] using attempt.symm
  subst r
  exact actual_scheduled_check_bound actual bound t ss q proper js hj xs answer

theorem fast_actual_singleton_check_bound (t s : Tree) (q : Nat) (F : Forest)
 (proper : ForestState.proper (some t) [s]=true) (answer : OrdinaryDispatch.FastOrdinary.solve q t s=some F) :
 (meterChecked (some t) [s] q F).work≤inspectionBill (some t) [s] q :=
 actual_singleton_check_bound _ fast_returned_payload t s q F proper answer

theorem fast_disjoint_attempt_check_bound (t : Tree) (ss : List Tree) (q : Nat)
 (proper : ForestState.proper (some t) ss=true) (r : PaidQueries.Receipt Forest)
 (attempt : disjointAttempt t ss (fun T S q=>OrdinaryDispatch.FastOrdinary.solve q T S) q=some r)
 (xs : List (Nat×Forest)) (answer : r.answers=some xs) :
 (meterChecked (some t) ss q (xs.flatMap Prod.snd)).work≤inspectionBill (some t) ss q :=
 disjoint_attempt_check_bound _ fast_returned_payload t ss q proper r attempt xs answer
end GenericForest.CheckCorrespondence
