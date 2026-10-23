/- Distinct double strong-induction reconstruction of the actual recursion.
All remaining local obligations are explicit theorem parameters. No instance
of these parameters is claimed, and no author local/global exactness is used. -/
import ReconstructionV2
open RMAF ForestState Universal233 Universal233.CherryBranching OrdinaryDispatch
namespace IndependentReconstruction
open OrdinaryDispatch.FastOrdinary

def OwnPaid (q : Nat) : Tree→Tree→Nat→Option CommonForest :=
 fun u v r => if hr : r<q then solve r u v else none

def BelowBudget (q : Nat) : Prop := ∀ r,r<q → ∀ T S,
 DepthOne.proper T S=true → QueryExact T S r (solve r T S)

def CommonReady : Prop := ∀ T S reverse c,
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.common reverse c →
 DepthOne.proper (commonPair T S reverse c).1 (commonPair T S reverse c).2=true ∧
 (leaves (commonPair T S reverse c).1).length<(leaves T).length

def CommonLift : Prop := ∀ q T S reverse c answer,
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.common reverse c →
 QueryExact (commonPair T S reverse c).1 (commonPair T S reverse c).2 q answer →
 QueryExact T S q (answer.map (expandCommon T S reverse c))

def OneRule : Prop := ∀ q T S reverse c,
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.one reverse c →
 BelowBudget q → QueryExact T S q (runChildren (OwnPaid q)
  (Oriented reverse T S).1 (Oriented reverse T S).2 q [pendantChild (Oriented reverse T S).2 c.a c.b])

def HighRule : Prop := ∀ q T S reverse c,
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.high reverse c →
 BelowBudget q → QueryExact T S q (runChildren (OwnPaid q)
  (Oriented reverse T S).1 (Oriented reverse T S).2 q (branches (Oriented reverse T S).2 c.a c.b))

def ForwardRule4 : Prop := ∀ q T S (s : Rule4.Choice T S),
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.rule4Forward s →
 BelowBudget q → QueryExact T S q (runRule4 (OwnPaid q) s q)

def ReverseRule4 : Prop := ∀ q T S (s : Rule4.Choice S T),
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.rule4Reverse s →
 BelowBudget q → QueryExact T S q (runRule4 (OwnPaid q) s q)

def Hard2Rule : Prop := ∀ q T S c d,
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.hard2 c d →
 BelowBudget q → QueryExact T S q (Hard2Dispatcher.run (OwnPaid q) T S c d q)

def RejectImpossible : Prop := ∀ T S,DepthOne.proper T S=true →
 DepthOne.pretest01 T S=.rejected → early T S≠.refused

theorem solve_exact_from_local_rules
 (ready : CommonReady) (lift : CommonLift) (one : OneRule) (high : HighRule)
 (forward4 : ForwardRule4) (reverse4 : ReverseRule4) (hard : Hard2Rule)
 (nonrefusal : RejectImpossible) (q : Nat) :
 ∀ T S,DepthOne.proper T S=true → QueryExact T S q (solve q T S) := by
 induction q using Nat.strong_induction_on with
 | h q lowerBudget =>
  have below : BelowBudget q := by
    intro r hr T S hp
    exact lowerBudget r hr T S hp
  have bySize : ∀ n T S,(leaves T).length≤n → DepthOne.proper T S=true →
      QueryExact T S q (solve q T S) := by
   intro n
   induction n using Nat.strong_induction_on with
   | h n lowerSize =>
    intro T S bound hp
    cases pre : DepthOne.pretest01 T S with
    | refused =>
      unfold DepthOne.pretest01 at pre
      simp only [hp,ite_true] at pre
      split at pre <;> cases pre
    | found c => exact actual_solve_successful_pretest q hp pre
    | rejected =>
      rw [solve.eq_def]
      simp only [hp,ite_true,pre]
      cases selected : early T S with
      | common reverse c =>
        have prepared := ready T S reverse c hp pre selected
        have size : (leaves (commonPair T S reverse c).1).length<n := by omega
        have small := lowerSize _ size (commonPair T S reverse c).1
          (commonPair T S reverse c).2 (Nat.le_refl _) prepared.1
        have expanded := lift q T S reverse c _ hp pre selected small
        simpa only [selected,prepared.2,dite_true] using expanded
      | one reverse c =>
        simpa only [selected,OwnPaid] using one q T S reverse c hp pre selected below
      | high reverse c =>
        simpa only [selected,OwnPaid] using high q T S reverse c hp pre selected below
      | rule4Forward s =>
        simpa only [selected,OwnPaid] using forward4 q T S s hp pre selected below
      | rule4Reverse s =>
        simpa only [selected,OwnPaid] using reverse4 q T S s hp pre selected below
      | hard2 c d =>
        simpa only [selected,OwnPaid] using hard q T S c d hp pre selected below
      | refused => exact False.elim (nonrefusal T S hp pre selected)
  intro T S hp
  exact bySize _ T S (Nat.le_refl _) hp
end IndependentReconstruction
