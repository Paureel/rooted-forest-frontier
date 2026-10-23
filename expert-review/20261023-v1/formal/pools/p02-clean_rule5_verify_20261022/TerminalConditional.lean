import PaidConditional

/- One-shot terminal reconstruction; only own and permitted support proof constants. -/
open RMAF Universal233 OrdinaryDispatch

namespace CleanRule5Verify20261022

theorem cutoff_below (q : Nat) (below : IndependentReconstruction.BelowBudget q) :
    Rule5OrdinaryDispatch.BelowIH q (IndependentReconstruction.OwnPaid q) := by
  intro r hr
  constructor
  · intro t s b F hb hp hanswer
    have hlt : b < q := Nat.lt_of_le_of_lt hb hr
    have hsolve : FastOrdinary.solve b t s = some F := by
      simpa only [IndependentReconstruction.OwnPaid, hlt, ↓reduceDIte] using hanswer
    have hex := below b hlt t s hp
    simpa only [hsolve, QueryExact] using hex
  · intro t s b G hb hp hG hbudget
    have hlt : b < q := Nat.lt_of_le_of_lt hb hr
    have hex := below b hlt t s hp
    cases hsolve : FastOrdinary.solve b t s with
    | none =>
        rw [hsolve] at hex
        have hbad := hex G hG
        omega
    | some F =>
        refine ⟨F, ?_⟩
        simp only [IndependentReconstruction.OwnPaid, hlt, ↓reduceDIte, hsolve]

theorem exactAnswer_query {T S : Tree} {q : Nat} {answer : Option (List (List Nat))}
    (h : Rule5OrdinaryDispatch.ExactAnswer T S q answer) : QueryExact T S q answer := by
  cases answer with
  | none =>
      intro G hG
      by_cases hb : G.length - 1 ≤ q
      · obtain ⟨F, hF, _⟩ := h.2 G hG hb
        contradiction
      · omega
  | some F => exact h.1 F rfl

theorem terminal_rule5 (survival : GuardedSurvival)
    (q : Nat) (T S : Tree) (c d : CherryBranching.Candidate)
    (proper : DepthOne.proper T S = true)
    (pretest : DepthOne.pretest01 T S = .rejected)
    (early : FastOrdinary.early T S = .hard2 c d)
    (graph : Hard2Overlap.runHard2 T S c = some .disjoint)
    (below : IndependentReconstruction.BelowBudget q)
    (twoGood : ((CherryBranching.pendantPartition S c.a c.b).filter
      (restrictionAgrees T S)).length = 2) :
    QueryExact T S q (Hard2Dispatcher.rule5Answer (IndependentReconstruction.OwnPaid q)
      T S c.a c.b q) := by
  let actual := IndependentReconstruction.OwnPaid q
  have smaller : Rule5OrdinaryDispatch.BelowIH q actual := cutoff_below q below
  have admitted := AdmittedRule5Author.actual_admitted_closed T S c d proper early graph twoGood
  have cherry := (CherryBranching.selected_actual
    (AdmittedRule5Author.early_hard2_guards T S c d early).1).1
  obtain ⟨nt, ns, same⟩ := Rule5Classification.properPair_parts
    (Rule5Classification.admitted_parts admitted).1
  obtain ⟨z, picked⟩ := PaidBuilderAuthor.actual_final_available T S c d
    proper pretest early graph twoGood
  have finalSound := Rule5FinalClassification.final_selected_sound cherry admitted picked
  obtain ⟨answer, hrun, hexact⟩ :
      ∃ answer, Rule5OrdinaryDispatch.runSelected actual T S c.a c.b q z = .answered answer ∧
        Rule5OrdinaryDispatch.ExactAnswer T S q answer := by
    cases z with
    | «prefix» s =>
        have hs : Rule5Classification.selectLocal T S c.a c.b = some s ∧ s ≠ .remaining := finalSound
        refine ⟨_, rfl, ?_⟩
        exact Rule5OrdinaryDispatch.children_exact actual smaller nt ns same
          (fun _ hc => Rule5OrdinaryDispatch.prefix_facts cherry hs.1 hs.2 hc)
          (fun _ hG => Rule5Classification.local_prefix_cover cherry hs.1 hs.2 hG)
    | remaining bad boundary =>
        cases boundary with
        | first u v =>
            refine ⟨_, rfl, ?_⟩
            exact Rule5OrdinaryDispatch.children_exact actual smaller nt ns same
              (fun _ hc => Rule5OrdinaryDispatch.first_facts cherry admitted picked hc)
              (fun _ hG => Rule5SourceOrientation.selected_first_cover cherry admitted picked hG)
        | third u v =>
            refine ⟨_, rfl, ?_⟩
            exact Rule5OrdinaryDispatch.children_exact actual smaller nt ns same
              (fun _ hc => Rule5OrdinaryDispatch.third_facts cherry admitted picked hc)
              (fun _ hG => Rule5SourceOrientation.selected_third_cover cherry admitted picked hG)
        | one edge =>
            refine ⟨_, rfl, ?_, ?_⟩
            · intro F hF
              exact Rule5CommonOrdinary.selected_sound_minimum cherry admitted picked actual q smaller hF
            · intro G hG hb
              exact Rule5CommonOrdinary.selected_complete cherry admitted picked actual q smaller G hG hb
        | second u v =>
            obtain ⟨R, built⟩ := PaidBuilderAuthor.actual_second_build_selected T S c d bad u v
              proper early graph picked
            refine ⟨Rule5PaidOrdinary.bestFor actual R q, ?_, paid_best_exact survival actual R q smaller⟩
            simp only [Rule5OrdinaryDispatch.runSelected, Rule5PaidOrdinary.solveSelected, built]
  have dispatched : Rule5OrdinaryDispatch.dispatch actual T S c.a c.b q = .answered answer := by
    simpa only [Rule5OrdinaryDispatch.dispatch, picked] using hrun
  have hanswer : Hard2Dispatcher.rule5Answer actual T S c.a c.b q = answer := by
    simp only [Hard2Dispatcher.rule5Answer, dispatched]
  change QueryExact T S q (Hard2Dispatcher.rule5Answer actual T S c.a c.b q)
  rw [hanswer]
  exact exactAnswer_query hexact

set_option pp.fullNames true in
#check terminal_rule5
#print axioms terminal_rule5

end CleanRule5Verify20261022
