import CoreProgram

/-! Actual candidate source-code facts. They prove normalization and a
one-cut trace for arbitrary pure source subtrees, not target agreement. -/
namespace ScaffoldProfiles.Source
open RMAF Universal233.CoreProgram

theorem homogeneous_source_normalizes (t : Tree) (color : Nat → Nat) (p : List Bool)
    (a : Nat) (h : ∀ x ∈ leaves t, color x = a) :
    normalize (fromTree color p t) = .leaf ⟨p, leaves t, a⟩ := by
  induction t generalizing p with
  | leaf x =>
    have hx := h x (by simp [leaves])
    simp [fromTree, normalize, leaves, hx]
  | node l r il ir =>
    have hl : ∀ x ∈ leaves l, color x = a := by
      intro x hx; exact h x (by simp [leaves, hx])
    have hr : ∀ x ∈ leaves r, color x = a := by
      intro x hx; exact h x (by simp [leaves, hx])
    simp [fromTree, normalize, il _ hl, ir _ hr, leaves]

/-- Once original pure subtrees normalize to the two root children, the
actual run detaches the first one at original edge ([] ,[false]). -/
theorem two_root_groups_one_cut (xs ys : List Nat) :
    (run 1 (.node [] (.leaf ⟨[false], xs, 0⟩) (.leaf ⟨[true], ys, 1⟩)) [] []).outputs =
      [⟨[xs,ys], [[false]]⟩] := by
  simp [run, step, normalize, choose, groups, attempt, erase, prefixRoot]

/-- Internal source shapes can be arbitrary while the same profile [1]
remains. The color-purity hypotheses are explicit; no target is mentioned. -/
theorem arbitrary_pure_subtrees_one_cut (l r : Tree) (color : Nat → Nat)
    (hl : ∀ x ∈ leaves l, color x = 0) (hr : ∀ x ∈ leaves r, color x = 1) :
    (run 1 (fromTree color [] (.node l r)) [] []).outputs =
      [⟨[leaves l, leaves r], [[false]]⟩] := by
  have hn : normalize (fromTree color [] (.node l r)) =
      .node [] (.leaf ⟨[false], leaves l, 0⟩) (.leaf ⟨[true], leaves r, 1⟩) := by
    simp [fromTree, normalize, homogeneous_source_normalizes l color [false] 0 hl,
      homogeneous_source_normalizes r color [true] 1 hr]
  simpa [run, step, hn, normalize, choose, groups, attempt, erase, prefixRoot] using
    two_root_groups_one_cut (leaves l) (leaves r)

#print axioms homogeneous_source_normalizes
#print axioms two_root_groups_one_cut
#print axioms arbitrary_pure_subtrees_one_cut
end ScaffoldProfiles.Source

namespace ScaffoldProfiles.Source
/-- Same original-label refinement direction required by the source consumer. -/
def Refines (P Q : List (List Nat)) : Prop :=
  ∀ S, S ∈ P → ∃ R, R ∈ Q ∧ ∀ x, x ∈ S → x ∈ R

/-- A covered source partition with a protected whole-color block forces
an emitted coarsening to retain that exact whole color. Source validity of
that test partition is a separate actual-graph obligation. -/
theorem whole_color_from_refinement (P Q : List (List Nat)) (labels S : List Nat)
    (color : Nat → Nat) (a x : Nat) (hx : x ∈ S) (hS : S ∈ P)
    (hcolor : ∀ y, y ∈ S ↔ y ∈ labels ∧ color y = a)
    (hQlabels : ∀ R ∈ Q, ∀ y ∈ R, y ∈ labels)
    (hQpure : ∀ R ∈ Q, ∀ y ∈ R, ∀ z ∈ R, color y = color z)
    (hcover : Refines P Q) :
    ∃ R, R ∈ Q ∧ ∀ y, y ∈ R ↔ y ∈ S := by
  obtain ⟨R,hR,hsub⟩ := hcover S hS
  refine ⟨R,hR,?_⟩
  intro y
  constructor
  · intro hy
    apply (hcolor y).mpr
    refine ⟨hQlabels R hR y hy,?_⟩
    exact (hQpure R hR y hy x (hsub x hx)).trans ((hcolor x).mp hx).2
  · exact hsub y

/-- The cardinality part of the generalized good-parent exchange. The
geometric/source agreement surgery is not proved by this lemma. -/
theorem exchange_component_budget (a b outside crosses : Nat)
    (ha : 2 ≤ a) (hc : crosses ≤ 1) :
    1 + b + crosses + outside ≤ a + b + outside := by omega

open RMAF Universal233.CoreProgram

def exchangeTarget : Tree :=
  .node (.node (.leaf 0) (.node (.leaf 2) (.leaf 3)))
        (.node (.leaf 1) (.node (.leaf 4) (.leaf 5)))
def exchangeSource : Tree :=
  .node (.node (.leaf 0) (.leaf 1))
        (.node (.node (.leaf 2) (.leaf 4)) (.node (.leaf 3) (.leaf 5)))

theorem generalized_exchange_positive_left :
    agreement exchangeTarget exchangeSource [[0,1],[2,3],[4],[5]] = true := by decide

theorem generalized_exchange_positive_right :
    agreement exchangeTarget exchangeSource [[0,1],[2],[3],[4,5]] = true := by decide

theorem false_onecut_color_partition_rejected :
    agreement exchangeTarget exchangeSource [[0,1],[2,3],[4,5]] = false := by decide

#print axioms whole_color_from_refinement
#print axioms exchange_component_budget
#print axioms generalized_exchange_positive_left
#print axioms generalized_exchange_positive_right
#print axioms false_onecut_color_partition_rejected
end ScaffoldProfiles.Source
