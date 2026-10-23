/- One-shot independently authored optimizer SOURCE-work join; shared support only. -/
import RebasedSourceCounter
import WholeFunctional
import RWFinal
import OptimizerSourceBodies
import Std.Tactic

namespace FreshOptimizerJoin20261022
open RMAF Universal233 OrdinaryDispatch Universal233.CoreWork
open OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.CompleteSource
open OrdinaryDispatch.GlobalSourceAssembly OrdinaryDispatch.OptimizerLocalWork
open OrdinaryDispatch.RecoveryLocalWork

theorem proper_parts (T S : Tree) (hp : DepthOne.proper T S = true) :
 (leaves T).Nodup ∧ (leaves S).Nodup ∧ (leaves T).Perm (leaves S) := by
 simp only [DepthOne.proper, Bool.and_eq_true, decide_eq_true_eq] at hp
 exact ⟨hp.1.1, hp.1.2, hp.2⟩

theorem nodes_identity (T : Tree) : treeNodes T + 1 = 2 * (leaves T).length := by
 induction T with
 | leaf x => simp [treeNodes, leaves]
 | node l r ihl ihr =>
   simp only [treeNodes, leaves, List.length_append]
   omega

theorem failed_length (start q : Nat) : (failedTrials start q).length = q := by
 induction q generalizing start with
 | zero => rfl
 | succ q ih => simp [failedTrials, ih]

theorem failed_budgets (start q : Nat) (t : Trial) (ht : t ∈ failedTrials start q) :
 start ≤ t.1 ∧ t.1 < start + q := by
 induction q generalizing start with
 | zero => simp [failedTrials] at ht
 | succ q ih =>
   simp only [failedTrials, List.mem_cons] at ht
   rcases ht with h | h
   · subst t; simp
   · have h' := ih (start+1) h
     omega

theorem add_le_add {a b c d : Rat} (h : a ≤ b) (g : c ≤ d) : a+c ≤ b+d :=
 Rat.le_trans (Rat.add_le_add_right.mpr h) (Rat.add_le_add_left.mpr g)

theorem base_step (q : Nat) : Rule5ActualTrace.base^q ≤ Rule5ActualTrace.base^(q+1) := by
 have h : (1:Rat) ≤ Rule5ActualTrace.base := by unfold Rule5ActualTrace.base; decide +kernel
 have hn : (0:Rat) ≤ Rule5ActualTrace.base^q := Rat.pow_nonneg (by unfold Rule5ActualTrace.base; decide +kernel)
 simpa only [Rat.mul_one, Rat.pow_succ] using Rat.mul_le_mul_of_nonneg_left h hn

theorem base_mono (a b : Nat) (h : a ≤ b) :
 Rule5ActualTrace.base^a ≤ Rule5ActualTrace.base^b := by
 induction b generalizing a with
 | zero =>
   have ha : a=0 := by omega
   subst a
   exact Rat.le_refl
 | succ b ih =>
   by_cases he : a=b+1
   · subst a; exact Rat.le_refl
   · exact Rat.le_trans (ih a (by omega)) (base_step b)

theorem base_one (q : Nat) : (1:Rat) ≤ Rule5ActualTrace.base^q := by
 simpa only [Rat.pow_zero] using base_mono 0 q (Nat.zero_le q)

theorem trials_sum_bound (w : Nat→Nat) (ts : List Trial) (M : Rat)
 (h : ∀ t ∈ ts, (w t.1:Rat) ≤ M) :
 (trialWork w ts:Rat) ≤ (ts.length:Rat)*M := by
 induction ts with
 | nil => simp [trialWork]
 | cons t ts ih =>
   have hh := h t (by simp)
   have tail := ih (fun u hu => h u (by simp [hu]))
   have hh' := add_le_add hh tail
   simpa [trialWork, Rat.add_mul, Rat.add_comm] using hh'

theorem wrapper_bound (n q : Nat) (hq : q < n) :
 preflightFee (2*n) + 12*(q+1) + 32 ≤ 512*(2*n+1)^2 := by
 have hs : 2*n+1 ≤ (2*n+1)^2 := by
   simpa [Nat.pow_succ] using Nat.le_mul_of_pos_right (2*n+1) (by omega : 0<2*n+1)
 have hm := Nat.mul_le_mul_left 256 hs
 simp only [preflightFee]
 omega

end FreshOptimizerJoin20261022
