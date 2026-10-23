import FourTransitions
import MergeControls

namespace TripleDP.Transitions.Restriction.Fixtures
open TripleDP.CostRoute TripleDP.Transitions.Controls

variable {α I : Type} {l r : BTree α}
set_option linter.unusedSimpArgs false

private theorem live_leaf (A : Family (.node l r) I) (side : Bool) (i : I)
    (x : α) (ht : child l r side = .leaf x) :
    Live A side i ↔ A.support i [side] := by
  simp [Live, ht, LeafAt]

private theorem live_cherry (A : Family (.node l r) I) (side : Bool) (i : I)
    (x y : α) (ht : child l r side = .node (.leaf x) (.leaf y)) :
    Live A side i ↔ A.support i [side, false] ∨ A.support i [side, true] := by
  constructor
  · rintro ⟨a, z, hz, ha⟩
    rw [ht] at hz
    cases a with
    | nil => exact False.elim hz
    | cons b a =>
      cases b with
      | false => have he : a = [] := hz.1; subst a; exact Or.inl ha
      | true => have he : a = [] := hz.1; subst a; exact Or.inr ha
  · rintro (ha | ha)
    · exact ⟨[false], x, by rw [ht]; exact ⟨rfl, rfl⟩, ha⟩
    · exact ⟨[true], y, by rw [ht]; exact ⟨rfl, rfl⟩, ha⟩

private theorem root_charge_one (A : Family (.node l r) I) (h : OpenBranchLive A)
    (side : Bool) (i : I) (hi : A.support i [side]) :
    boundaryCharge (restrict A h side).boundary = 1 := by
  have hb := (restrict_boundary_iff A h side
    ⟨i, occupied_live A h i side ⟨[], hi⟩⟩).mpr hi
  rw [hb]
  rfl

private theorem root_charge_zero (A : Family (.node l r) I) (h : OpenBranchLive A)
    (side : Bool) (hi : ∀ i, ¬ A.support i [side]) :
    boundaryCharge (restrict A h side).boundary = 0 := by
  cases hb : (restrict A h side).boundary with
  | none => rfl
  | some i => exact False.elim (hi i.val ((restrict_boundary_iff A h side i).mp hb))

def R1 := closeBoth (Controls.singleton "a") (Controls.singleton "b")
def R2 := extendLeft (Controls.singleton "a") (Controls.singleton "b") () rfl
def R3 := extendRight (Controls.singleton "a") (Controls.singleton "b") () rfl
def R4 := merge (Controls.singleton "a") (Controls.singleton "b") () () rfl rfl
def R5 := closeBoth (merge (Controls.singleton "a") (Controls.singleton "b") () () rfl rfl) (Controls.singleton "c")
def R6 := closeBoth (closeBoth (Controls.singleton "a") (Controls.singleton "b")) (Controls.singleton "c")
def R7 := extendLeft (Controls.singleton "a") (closeBoth (Controls.singleton "b") (Controls.singleton "c")) () rfl
def R8 := merge (extendLeft (Controls.singleton "x") (Controls.singleton "x") () rfl)
  (extendRight (Controls.singleton "x") (Controls.singleton "x") () rfl) (.inl ()) (.inr ()) rfl rfl

theorem H1 : OpenBranchLive R1 := closeBoth_normal _ _
theorem H2 : OpenBranchLive R2 := extendLeft_normal _ _ _ _
theorem H3 : OpenBranchLive R3 := extendRight_normal _ _ _ _
theorem H4 : OpenBranchLive R4 := merge_normal _ _ _ _ _ _
theorem H5 : OpenBranchLive R5 := closeBoth_normal _ _
theorem H6 : OpenBranchLive R6 := closeBoth_normal _ _
theorem H7 : OpenBranchLive R7 := extendLeft_normal _ _ _ _
theorem H8 : OpenBranchLive R8 := merge_normal _ _ _ _ _ _

private theorem R1_left_count : (restrict R1 H1 false).blockCount = 1 := by
  classical
  rw [restrict_count]
  have hh (i) := live_leaf R1 false i "a" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R1 false i)) = (fun i => decide (R1.support i [false])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R1, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R1_left_charge : boundaryCharge (restrict R1 H1 false).boundary = 1 := by
  apply root_charge_one R1 H1 false (.inl ())
  simp [R1, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R1_right_count : (restrict R1 H1 true).blockCount = 1 := by
  classical
  rw [restrict_count]
  have hh (i) := live_leaf R1 true i "b" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R1 true i)) = (fun i => decide (R1.support i [true])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R1, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R1_right_charge : boundaryCharge (restrict R1 H1 true).boundary = 1 := by
  apply root_charge_one R1 H1 true (.inr ())
  simp [R1, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

theorem R1_numbers : R1.blockCount = 2 ∧ R1.cost = 2 ∧
    (restrict R1 H1 false).blockCount = 1 ∧ (restrict R1 H1 true).blockCount = 1 ∧
    (restrict R1 H1 false).cost = 0 ∧ (restrict R1 H1 true).cost = 0 ∧
    boundaryCharge (restrict R1 H1 false).boundary = 1 ∧
    boundaryCharge (restrict R1 H1 true).boundary = 1 := by
  refine ⟨by decide, by decide, R1_left_count, R1_right_count, ?_, ?_, R1_left_charge, R1_right_charge⟩
  · simp only [Family.cost, R1_left_count, R1_left_charge]
  · simp only [Family.cost, R1_right_count, R1_right_charge]

private theorem R2_left_count : (restrict R2 H2 false).blockCount = 1 := by
  classical
  rw [restrict_count]
  have hh (i) := live_leaf R2 false i "a" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R2 false i)) = (fun i => decide (R2.support i [false])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R2, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R2_left_charge : boundaryCharge (restrict R2 H2 false).boundary = 1 := by
  apply root_charge_one R2 H2 false (.inl ())
  simp [R2, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R2_right_count : (restrict R2 H2 true).blockCount = 1 := by
  classical
  rw [restrict_count]
  have hh (i) := live_leaf R2 true i "b" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R2 true i)) = (fun i => decide (R2.support i [true])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R2, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R2_right_charge : boundaryCharge (restrict R2 H2 true).boundary = 1 := by
  apply root_charge_one R2 H2 true (.inr ())
  simp [R2, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

theorem R2_numbers : R2.blockCount = 2 ∧ R2.cost = 1 ∧
    (restrict R2 H2 false).blockCount = 1 ∧ (restrict R2 H2 true).blockCount = 1 ∧
    (restrict R2 H2 false).cost = 0 ∧ (restrict R2 H2 true).cost = 0 ∧
    boundaryCharge (restrict R2 H2 false).boundary = 1 ∧
    boundaryCharge (restrict R2 H2 true).boundary = 1 := by
  refine ⟨by decide, by decide, R2_left_count, R2_right_count, ?_, ?_, R2_left_charge, R2_right_charge⟩
  · simp only [Family.cost, R2_left_count, R2_left_charge]
  · simp only [Family.cost, R2_right_count, R2_right_charge]

private theorem R3_left_count : (restrict R3 H3 false).blockCount = 1 := by
  classical
  rw [restrict_count]
  have hh (i) := live_leaf R3 false i "a" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R3 false i)) = (fun i => decide (R3.support i [false])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R3, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R3_left_charge : boundaryCharge (restrict R3 H3 false).boundary = 1 := by
  apply root_charge_one R3 H3 false (.inl ())
  simp [R3, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R3_right_count : (restrict R3 H3 true).blockCount = 1 := by
  classical
  rw [restrict_count]
  have hh (i) := live_leaf R3 true i "b" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R3 true i)) = (fun i => decide (R3.support i [true])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R3, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R3_right_charge : boundaryCharge (restrict R3 H3 true).boundary = 1 := by
  apply root_charge_one R3 H3 true (.inr ())
  simp [R3, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

theorem R3_numbers : R3.blockCount = 2 ∧ R3.cost = 1 ∧
    (restrict R3 H3 false).blockCount = 1 ∧ (restrict R3 H3 true).blockCount = 1 ∧
    (restrict R3 H3 false).cost = 0 ∧ (restrict R3 H3 true).cost = 0 ∧
    boundaryCharge (restrict R3 H3 false).boundary = 1 ∧
    boundaryCharge (restrict R3 H3 true).boundary = 1 := by
  refine ⟨by decide, by decide, R3_left_count, R3_right_count, ?_, ?_, R3_left_charge, R3_right_charge⟩
  · simp only [Family.cost, R3_left_count, R3_left_charge]
  · simp only [Family.cost, R3_right_count, R3_right_charge]

private theorem R4_left_count : (restrict R4 H4 false).blockCount = 1 := by
  classical
  rw [restrict_count]
  have hh (i) := live_leaf R4 false i "a" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R4 false i)) = (fun i => decide (R4.support i [false])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R4, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R4_left_charge : boundaryCharge (restrict R4 H4 false).boundary = 1 := by
  apply root_charge_one R4 H4 false (.inl ())
  simp [R4, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R4_right_count : (restrict R4 H4 true).blockCount = 1 := by
  classical
  rw [restrict_count]
  have hh (i) := live_leaf R4 true i "b" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R4 true i)) = (fun i => decide (R4.support i [true])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R4, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R4_right_charge : boundaryCharge (restrict R4 H4 true).boundary = 1 := by
  apply root_charge_one R4 H4 true (.inl ())
  simp [R4, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

theorem R4_numbers : R4.blockCount = 1 ∧ R4.cost = 0 ∧
    (restrict R4 H4 false).blockCount = 1 ∧ (restrict R4 H4 true).blockCount = 1 ∧
    (restrict R4 H4 false).cost = 0 ∧ (restrict R4 H4 true).cost = 0 ∧
    boundaryCharge (restrict R4 H4 false).boundary = 1 ∧
    boundaryCharge (restrict R4 H4 true).boundary = 1 := by
  refine ⟨by decide, by decide, R4_left_count, R4_right_count, ?_, ?_, R4_left_charge, R4_right_charge⟩
  · simp only [Family.cost, R4_left_count, R4_left_charge]
  · simp only [Family.cost, R4_right_count, R4_right_charge]

private theorem R5_left_count : (restrict R5 H5 false).blockCount = 1 := by
  classical
  rw [restrict_count]
  have hh (i) := live_cherry R5 false i "a" "b" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R5 false i)) = (fun i => decide (R5.support i [false, false] ∨ R5.support i [false, true])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R5, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R5_left_charge : boundaryCharge (restrict R5 H5 false).boundary = 1 := by
  apply root_charge_one R5 H5 false (.inl (.inl ()))
  simp [R5, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R5_right_count : (restrict R5 H5 true).blockCount = 1 := by
  classical
  rw [restrict_count]
  have hh (i) := live_leaf R5 true i "c" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R5 true i)) = (fun i => decide (R5.support i [true])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R5, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R5_right_charge : boundaryCharge (restrict R5 H5 true).boundary = 1 := by
  apply root_charge_one R5 H5 true (.inr ())
  simp [R5, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

theorem R5_numbers : R5.blockCount = 2 ∧ R5.cost = 2 ∧
    (restrict R5 H5 false).blockCount = 1 ∧ (restrict R5 H5 true).blockCount = 1 ∧
    (restrict R5 H5 false).cost = 0 ∧ (restrict R5 H5 true).cost = 0 ∧
    boundaryCharge (restrict R5 H5 false).boundary = 1 ∧
    boundaryCharge (restrict R5 H5 true).boundary = 1 := by
  refine ⟨by decide, by decide, R5_left_count, R5_right_count, ?_, ?_, R5_left_charge, R5_right_charge⟩
  · simp only [Family.cost, R5_left_count, R5_left_charge]
  · simp only [Family.cost, R5_right_count, R5_right_charge]

private theorem R6_left_count : (restrict R6 H6 false).blockCount = 2 := by
  classical
  rw [restrict_count]
  have hh (i) := live_cherry R6 false i "a" "b" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R6 false i)) = (fun i => decide (R6.support i [false, false] ∨ R6.support i [false, true])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R6, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R6_left_charge : boundaryCharge (restrict R6 H6 false).boundary = 0 := by
  apply root_charge_zero
  intro i
  cases i with
  | inl i => cases i <;> simp [R6, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]
  | inr i => simp [R6, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R6_right_count : (restrict R6 H6 true).blockCount = 1 := by
  classical
  rw [restrict_count]
  have hh (i) := live_leaf R6 true i "c" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R6 true i)) = (fun i => decide (R6.support i [true])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R6, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R6_right_charge : boundaryCharge (restrict R6 H6 true).boundary = 1 := by
  apply root_charge_one R6 H6 true (.inr ())
  simp [R6, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

theorem R6_numbers : R6.blockCount = 3 ∧ R6.cost = 3 ∧
    (restrict R6 H6 false).blockCount = 2 ∧ (restrict R6 H6 true).blockCount = 1 ∧
    (restrict R6 H6 false).cost = 2 ∧ (restrict R6 H6 true).cost = 0 ∧
    boundaryCharge (restrict R6 H6 false).boundary = 0 ∧
    boundaryCharge (restrict R6 H6 true).boundary = 1 := by
  refine ⟨by decide, by decide, R6_left_count, R6_right_count, ?_, ?_, R6_left_charge, R6_right_charge⟩
  · simp only [Family.cost, R6_left_count, R6_left_charge]
  · simp only [Family.cost, R6_right_count, R6_right_charge]

private theorem R7_left_count : (restrict R7 H7 false).blockCount = 1 := by
  classical
  rw [restrict_count]
  have hh (i) := live_leaf R7 false i "a" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R7 false i)) = (fun i => decide (R7.support i [false])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R7, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R7_left_charge : boundaryCharge (restrict R7 H7 false).boundary = 1 := by
  apply root_charge_one R7 H7 false (.inl ())
  simp [R7, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R7_right_count : (restrict R7 H7 true).blockCount = 2 := by
  classical
  rw [restrict_count]
  have hh (i) := live_cherry R7 true i "b" "c" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R7 true i)) = (fun i => decide (R7.support i [true, false] ∨ R7.support i [true, true])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R7, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R7_right_charge : boundaryCharge (restrict R7 H7 true).boundary = 0 := by
  apply root_charge_zero
  intro i
  cases i with
  | inl i => simp [R7, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]
  | inr i => cases i <;> simp [R7, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

theorem R7_numbers : R7.blockCount = 3 ∧ R7.cost = 2 ∧
    (restrict R7 H7 false).blockCount = 1 ∧ (restrict R7 H7 true).blockCount = 2 ∧
    (restrict R7 H7 false).cost = 0 ∧ (restrict R7 H7 true).cost = 2 ∧
    boundaryCharge (restrict R7 H7 false).boundary = 1 ∧
    boundaryCharge (restrict R7 H7 true).boundary = 0 := by
  refine ⟨by decide, by decide, R7_left_count, R7_right_count, ?_, ?_, R7_left_charge, R7_right_charge⟩
  · simp only [Family.cost, R7_left_count, R7_left_charge]
  · simp only [Family.cost, R7_right_count, R7_right_charge]

private theorem R8_left_count : (restrict R8 H8 false).blockCount = 2 := by
  classical
  rw [restrict_count]
  have hh (i) := live_cherry R8 false i "x" "x" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R8 false i)) = (fun i => decide (R8.support i [false, false] ∨ R8.support i [false, true])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R8, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R8_left_charge : boundaryCharge (restrict R8 H8 false).boundary = 1 := by
  apply root_charge_one R8 H8 false (.inl (.inl ()))
  simp [R8, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R8_right_count : (restrict R8 H8 true).blockCount = 2 := by
  classical
  rw [restrict_count]
  have hh (i) := live_cherry R8 true i "x" "x" rfl
  unfold liveIndices
  have he : (fun i => decide (Live R8 true i)) = (fun i => decide (R8.support i [true, false] ∨ R8.support i [true, true])) := by
    funext i
    exact decide_eq_decide.mpr (hh i)
  rw [he]
  simp [R8, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

private theorem R8_right_charge : boundaryCharge (restrict R8 H8 true).boundary = 1 := by
  apply root_charge_one R8 H8 true (.inl (.inl ()))
  simp [R8, closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, Controls.singleton, indexSum, selectIndex, selectedElems]

theorem R8_numbers : R8.blockCount = 3 ∧ R8.cost = 2 ∧
    (restrict R8 H8 false).blockCount = 2 ∧ (restrict R8 H8 true).blockCount = 2 ∧
    (restrict R8 H8 false).cost = 1 ∧ (restrict R8 H8 true).cost = 1 ∧
    boundaryCharge (restrict R8 H8 false).boundary = 1 ∧
    boundaryCharge (restrict R8 H8 true).boundary = 1 := by
  refine ⟨by decide, by decide, R8_left_count, R8_right_count, ?_, ?_, R8_left_charge, R8_right_charge⟩
  · simp only [Family.cost, R8_left_count, R8_left_charge]
  · simp only [Family.cost, R8_right_count, R8_right_charge]

#print axioms R1_numbers
#print axioms R2_numbers
#print axioms R3_numbers
#print axioms R4_numbers
#print axioms R5_numbers
#print axioms R6_numbers
#print axioms R7_numbers
#print axioms R8_numbers
end TripleDP.Transitions.Restriction.Fixtures
