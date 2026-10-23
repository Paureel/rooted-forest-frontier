import Rule4Solve
import LocalExact
namespace OrdinaryDispatch
open RMAF Universal233

def rule4Child (actual : Tree → Tree → Nat → Option GenericForest.Forest)
    (b : Rule4.Branch) (r : Nat) : Option GenericForest.Forest :=
  GenericForest.solve actual (some b.target) b.sourceForest r

def runRule4 (actual : Tree → Tree → Nat → Option GenericForest.Forest)
    {T S : Tree} (s : Rule4.Choice T S) (q : Nat) : Option GenericForest.Forest :=
  Rule4.solveForest s q (rule4Child actual)

theorem rule4_child_exact_at (actual : Tree → Tree → Nat → Option GenericForest.Forest)
    (b : Rule4.Branch) (r : Nat) (ih : ForestMinCompletion.LocalOrdinaryIH r actual) :
    Rule4.ExactChild (rule4Child actual) b r := by
  have exactness := GenericForest.LocalIH.exact_at_budget_bound r actual ih
  refine ⟨?_,?_⟩
  · intro G hG
    have hs := GenericForest.solve_sound actual (some b.target) b.sourceForest r G hG
    refine ⟨hs,?_⟩
    intro H hH
    obtain ⟨F,hF,least⟩ := exactness.2 (some b.target) b.sourceForest r H (Nat.le_refl _) hH.1 hH.2
    have eq : F=G := Option.some.inj (hF.symm.trans hG)
    simpa [eq] using least
  · intro H hH
    exact exactness.2 (some b.target) b.sourceForest r H (Nat.le_refl _) hH.1 hH.2

theorem runRule4_minimum (actual : Tree → Tree → Nat → Option GenericForest.Forest)
    {T S : Tree} (s : Rule4.Choice T S) (q : Nat)
    (ih : ∀r,r<q → ForestMinCompletion.LocalOrdinaryIH r actual)
    (G : GenericForest.Forest) (hG : runRule4 actual s q=some G) :
    agreement T S G=true ∧ G.length-1≤q ∧
      ∀ F,agreement T S F=true → F.length-1≤q → G.length≤F.length := by
  exact Rule4.solveForest_minimum s q (rule4Child actual)
    (fun b hb hq => rule4_child_exact_at actual b _ (ih _ (Rule4.actual_callback_decrease s q b hb hq))) G hG

theorem runRule4_complete (actual : Tree → Tree → Nat → Option GenericForest.Forest)
    {T S : Tree} (s : Rule4.Choice T S) (q : Nat)
    (ih : ∀r,r<q → ForestMinCompletion.LocalOrdinaryIH r actual)
    (F : GenericForest.Forest) (hF : agreement T S F=true) (hq : F.length-1≤q) :
    ∃ G,runRule4 actual s q=some G := by
  exact Rule4.solveForest_exists s q (rule4Child actual)
    (fun b hb hbq => rule4_child_exact_at actual b _ (ih _ (Rule4.actual_callback_decrease s q b hb hbq))) F hF hq
end OrdinaryDispatch
