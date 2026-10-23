import BOScan
namespace OrdinaryDispatch.BudgetOptimization
open RMAF Universal233 RestrictionBridge

structure Execution where
 search : Scan
 output : Option CoreProgram.Output
 recoveries : List (CommonForest × Option CoreProgram.Output)
 deriving Repr

/-- Only the selected minimum forest reaches this one-time final recovery. -/
def finish (S : Tree) (r : Scan) : Execution :=
 match r.selected with
 | none => ⟨r,none,[]⟩
 | some (_,F) =>
   let answer := FinalCutRecovery.recover S F
   ⟨r,answer,[(F,answer)]⟩

@[simp] theorem finish_search (S : Tree) (r : Scan) : (finish S r).search=r := by
 cases h : r.selected with
 | none => simp [finish,h]
 | some p => cases p;simp [finish,h]

/-- Total original-tree optimizer. Proper inputs query budgets 0 through n-1,
stopping at the first success. Malformed inputs refuse before any query. -/
def optimize (T S : Tree) : Execution :=
 if DepthOne.proper T S then
   finish S (scan (fun q => FastOrdinary.solve q T S) 0 (leaves T).length)
 else ⟨⟨none,[]⟩,none,[]⟩

theorem malformed (T S : Tree) (hp : DepthOne.proper T S=false) :
 (optimize T S).search.trials=[] ∧ (optimize T S).recoveries=[] ∧
 (optimize T S).output=none := by simp [optimize,hp]

theorem scan_upper_success (T S : Tree) (hp : DepthOne.proper T S=true) :
 ∃q F,(scan (fun q => FastOrdinary.solve q T S) 0 (leaves T).length).selected=some (q,F) := by
 have af := singletons_agreement T S hp
 have ex := FastOrdinary.query_complete
   (FastOrdinary.solve_exact ((leaves T).length-1) T S hp)
   (singletons (leaves T)) af (by simp [singletons])
 have pos : 0<(leaves T).length := List.length_pos_iff.2 (leaves_nonempty T)
 exact scan_complete _ (leaves T).length 0 ((leaves T).length-1) (by omega) (by omega) ex

theorem selected_minimum (T S : Tree) (hp : DepthOne.proper T S=true) (q : Nat) (F : CommonForest)
 (chosen : (scan (fun q => FastOrdinary.solve q T S) 0 (leaves T).length).selected=some (q,F)) :
 agreement T S F=true ∧ F.length=q+1 ∧
 (∀G,agreement T S G=true → F.length≤G.length) ∧ q<(leaves T).length ∧
 (scan (fun q => FastOrdinary.solve q T S) 0 (leaves T).length).trials=
   failedTrials 0 q++[(q,some F)] ∧
 (∀b,b<q → FastOrdinary.solve b T S=none) := by
 obtain ⟨sk,eq,lt,tr,yes,no⟩ := scan_success _ _ 0 q F chosen
 have sq : sk=q := by omega
 subst sk
 have exactness := FastOrdinary.query_sound (FastOrdinary.solve_exact q T S hp) yes
 have pos := FastOrdinary.original_positive exactness.1
 have lower : q≤F.length-1 := by
   by_cases zero : q=0
   · omega
   · have refused := no (q-1) (by omega) (by omega)
     have h := FastOrdinary.solve_exact (q-1) T S hp
     rw [refused] at h
     have cut := h F exactness.1
     omega
 exact ⟨exactness.1,by omega,exactness.2.2,by omega,tr,fun b hb => no b (by omega) hb⟩

/-- Actual final call and every query trial, original edges, nonredundant
components, and global optimality. There is no supplied optimum oracle. -/
theorem optimization_exact (T S : Tree) (hp : DepthOne.proper T S=true) :
 ∃q F o,
 (optimize T S).search.selected=some (q,F) ∧
 (optimize T S).search.trials=failedTrials 0 q++[(q,some F)] ∧
 (optimize T S).output=some o ∧ (optimize T S).recoveries=[(F,some o)] ∧
 FastOrdinary.solve q T S=some F ∧ FinalCutRecovery.recover S F=some o ∧
 agreement T S F=true ∧ agreement T S o.partition=true ∧
 CutRealization.RealizedOutput S o ∧
 o.sourceCuts.Nodup ∧ (∀e,e∈o.sourceCuts → CoreGraph.Valid S e ∧ e≠[]) ∧
 o.sourceCuts.length=q ∧ o.partition.length=q+1 ∧
 (∀G,agreement T S G=true → o.partition.length≤G.length) ∧ q<(leaves T).length := by
 obtain ⟨q,F,chosen⟩ := scan_upper_success T S hp
 obtain ⟨af,len,minimum,bound,tr,no⟩ := selected_minimum T S hp q F chosen
 have yes := (scan_success _ _ 0 q F chosen).choose_spec.2.2.2.1
 obtain ⟨o,recovered,oaf,cuts,parts,realized,perm⟩ :=
   FinalCutRecovery.recover_original_agreement T S F ((DepthOne.proper_iff T S).1 hp).2.1 af
 have edges := FinalCutRecovery.recover_edges S F o recovered
 refine ⟨q,F,o,?_,?_,?_,?_,yes,recovered,af,oaf,realized,edges.1,edges.2,
   by omega,by omega,fun G hG => parts ▸ minimum G hG,bound⟩
 all_goals simp [optimize,hp,finish,chosen,recovered,tr]

/-- q=0 is permitted, but external k=0 remains refused before its query. -/
theorem external_zero_guard (T S : Tree) : FastOrdinary.external T S 0=none := rfl

theorem actual_query_count (T S : Tree) (hp : DepthOne.proper T S=true) :
 ∃q F,(optimize T S).search.selected=some (q,F) ∧
 (optimize T S).search.trials.length=q+1 ∧
 ((optimize T S).search.trials.filter (fun t => t.2.isNone)).length=q ∧
 (optimize T S).recoveries.length=1 := by
 obtain ⟨q,F,o,sel,tr,out,rec,rest⟩ := optimization_exact T S hp
 have fail : ∀start n,((failedTrials start n).filter (fun t => t.2.isNone)).length=n := by
   intro start n
   induction n generalizing start with
   | zero => rfl
   | succ n ih => simp [failedTrials,ih]
 exact ⟨q,F,sel,by simp [tr,failed_length],by simp [tr,List.filter_append,fail],by simp [rec]⟩

end OrdinaryDispatch.BudgetOptimization

namespace OrdinaryDispatch.BudgetOptimization
open RMAF Universal233

/-- The new wrapper agrees with the exact sealed external API at its selected
positive component budget; it does not recover cuts at each failed trial. -/
theorem external_at_selected (T S : Tree) (hp : DepthOne.proper T S=true) :
 ∃q F,(optimize T S).search.selected=some (q,F) ∧
 (optimize T S).output=FastOrdinary.external T S (q+1) := by
 obtain ⟨q,F,o,sel,tr,out,rec,yes,recovered,rest⟩ := optimization_exact T S hp
 refine ⟨q,F,sel,?_⟩
 rw [out]
 simp [FastOrdinary.external,FastOrdinary.externalWith,yes,recovered]

end OrdinaryDispatch.BudgetOptimization
