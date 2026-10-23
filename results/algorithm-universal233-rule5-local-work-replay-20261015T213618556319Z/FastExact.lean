import FastSolve
import ExternalRecovery
namespace OrdinaryDispatch.FastOrdinary
open RMAF ForestState Universal233 Universal233.CherryBranching

theorem solve_malformed (q : Nat) (T S : Tree) (hp : DepthOne.proper T S=false) :
 solve q T S=none := by
 rw [solve.eq_def]
 simp [hp]

theorem solve_exact (q : Nat) (T S : Tree) (hp : DepthOne.proper T S=true) :
 QueryExact T S q (solve q T S) := by
 have below : ∀r,r<q →ForestMinCompletion.LocalOrdinaryIH r (cutoff solve q) := by
   intro r hr
   apply cutoff_local solve q ?_ r hr
   intro b hb t s proper
   exact solve_exact b t s proper
 rw [solve.eq_def]
 simp only [hp,ite_true]
 cases pre : DepthOne.pretest01 T S with
 | refused =>
   have no := (DepthOne.refused_iff T S).1 pre
   rw [hp] at no
   contradiction
 | found edge =>
   simp only [pre]
   exact found_query_exact T S q edge pre
 | rejected =>
   simp only [pre]
   have sound := early_sound T S
   cases selected : early T S with
   | common reverse c =>
     rw [selected] at sound
     have ready := common_pair_ready hp sound
     have smaller := solve_exact q (commonPair T S reverse c).1 (commonPair T S reverse c).2 ready.1
     have full := common_pair_exact hp sound q _ smaller
     simpa only [selected,ready.2,dite_true] using full
   | one reverse c =>
     rw [selected] at sound
     apply oriented_query_reverse (reverse:=reverse)
     exact selected_one_query_exact (cutoff solve q) (oriented_proper hp reverse) sound q below
   | high reverse c =>
     rw [selected] at sound
     apply oriented_query_reverse (reverse:=reverse)
     exact selected_high_query_exact (cutoff solve q) (oriented_proper hp reverse) sound q below
   | rule4Forward s => exact rule4_query_exact (cutoff solve q) s q below
   | rule4Reverse s => exact query_reverse (rule4_query_exact (cutoff solve q) s q below)
   | hard2 c d =>
     rw [selected] at sound
     exact Hard2Dispatcher.run_exact hp sound.1 sound.2.1 sound.2.2.1 sound.2.2.2 pre below
   | refused => exact False.elim (early_exhaustive hp pre selected)
termination_by (q,(leaves T).length)
decreasing_by
 all_goals simp_wf
 all_goals first | apply Prod.Lex.left; assumption | exact Prod.Lex.right _ ready.2

theorem actual_ordinary_IH : GenericForest.OrdinaryIH (fun T S q => solve q T S) := by
 constructor
 · intro T S q F proper answer
   exact query_sound (solve_exact q T S proper) answer
 · intro T S q F proper af budget
   exact query_complete (solve_exact q T S proper) F af budget

theorem actual_local_ordinary_IH (K : Nat) :
 ForestMinCompletion.LocalOrdinaryIH K (fun T S q => solve q T S) := by
 constructor
 · intro T S q F _ proper answer
   exact query_sound (solve_exact q T S proper) answer
 · intro T S q F _ proper af budget
   exact query_complete (solve_exact q T S proper) F af budget

/-- The unchanged full-current-source-forest program now consumes the actual
closed ordinary recursion, rather than an assumed ordinary oracle. -/
theorem actual_forest_exact :
 (∀T ss q F,GenericForest.solve (fun t s r => solve r t s) T ss q=some F →
   ForestState.agrees T ss F=true ∧ ForestState.additionalCost ss F≤q) ∧
 (∀T ss q G,ForestState.agrees T ss G=true → ForestState.additionalCost ss G≤q →
   ∃F,GenericForest.solve (fun t s r => solve r t s) T ss q=some F ∧ F.length≤G.length) :=
 GenericForest.exact_of_ordinary (fun t s r => solve r t s) actual_ordinary_IH

theorem actual_forest_minimum (T : Option Tree) (ss : List Tree) (q : Nat) {F : CommonForest}
 (returned : GenericForest.solve (fun t s r => solve r t s) T ss q=some F) :
 ∀G,ForestState.agrees T ss G=true → F.length≤G.length := by
 have sound := actual_forest_exact.1 T ss q F returned
 intro G ha
 by_cases budget : ForestState.additionalCost ss G≤q
 · obtain ⟨H,hH,len⟩ := actual_forest_exact.2 T ss q G ha budget
   have eq : H=F := Option.some.inj (hH.symm.trans returned)
   simpa [eq] using len
 · simp only [ForestState.additionalCost] at sound budget
   omega

def external (T S : Tree) (k : Nat) : Option CoreProgram.Output := externalWith solve T S k

theorem external_zero (T S : Tree) : external T S 0=none := rfl

theorem external_malformed (T S : Tree) (k : Nat) (hp : DepthOne.proper T S=false) :
 external T S k=none := by
 simp [external,externalWith,solve_malformed (k-1) T S hp]

theorem external_exact (T S : Tree) (k : Nat) (hp : DepthOne.proper T S=true) :
 ExternalExact T S k (external T S k) :=
 externalWith_exact solve T S k hp (fun _ => solve_exact (k-1) T S hp)

theorem external_original_edges (T S : Tree) (k : Nat) {o : CoreProgram.Output}
 (h : external T S k=some o) :
 o.sourceCuts.Nodup ∧ ∀e,e∈o.sourceCuts → CoreGraph.Valid S e ∧ e≠[] :=
 externalWith_edges solve T S k h
end OrdinaryDispatch.FastOrdinary
