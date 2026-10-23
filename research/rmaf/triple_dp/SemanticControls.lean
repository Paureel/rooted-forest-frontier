import RMAF

/-! Concrete semantic controls deliberately reuse the earlier executable RMAF
definition. They are kernel checks in that shared model, not an independent
graph-definition proof. Canonical-three-leaf exhaustion still needs a general
relabeling and shape-classification interface for a universal triple theorem. -/

namespace TripleSemanticControls
open RMAF

def tripleTrees : List Tree :=
  [.node (.node (.leaf 0) (.leaf 1)) (.leaf 2),
   .node (.node (.leaf 0) (.leaf 2)) (.leaf 1),
   .node (.node (.leaf 1) (.leaf 2)) (.leaf 0)]

def properPartitions : List (List (List Nat)) :=
  [[[0], [1], [2]], [[0, 1], [2]], [[0, 2], [1]], [[1, 2], [0]]]

theorem canonical_proper_triples :
    tripleTrees.all (fun t => tripleTrees.all (fun u =>
      properPartitions.all (agreement t u))) = true := by decide

theorem proper_triple_valid (t u : Tree) (p : List (List Nat))
    (ht : t ∈ tripleTrees) (hu : u ∈ tripleTrees) (hp : p ∈ properPartitions) :
    agreement t u p = true := by
  have h1 := List.all_eq_true.mp canonical_proper_triples t ht
  have h2 := List.all_eq_true.mp h1 u hu
  exact List.all_eq_true.mp h2 p hp

theorem bad_full_triple_rejected :
    agreement (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
      (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1)) [[0, 1, 2]] = false := by decide

inductive TripleShape where
  | ab | ac | bc
  deriving DecidableEq

inductive ProperCut where
  | singletons | ab | ac | bc
  deriving DecidableEq

def labelledTriple (a b c : Nat) : TripleShape → Tree
  | .ab => .node (.node (.leaf a) (.leaf b)) (.leaf c)
  | .ac => .node (.node (.leaf a) (.leaf c)) (.leaf b)
  | .bc => .node (.node (.leaf b) (.leaf c)) (.leaf a)

def labelledPartition (a b c : Nat) : ProperCut → List (List Nat)
  | .singletons => [[a], [b], [c]]
  | .ab => [[a, b], [c]]
  | .ac => [[a, c], [b]]
  | .bc => [[b, c], [a]]

/-- Arbitrary distinct labels, all three rooted triple shapes, every proper
partition: local agreement and source/target vertex disjointness hold.
The remaining interface is classification of every well-labelled 3-leaf tree
up to sibling swaps as one of these shapes, and graph-model correspondence. -/
theorem arbitrary_label_proper_triples (a b c : Nat)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (left right : TripleShape) (cut : ProperCut) :
    agreement (labelledTriple a b c left) (labelledTriple a b c right)
      (labelledPartition a b c cut) = true := by
  have hba := Ne.symm hab
  have hca := Ne.symm hac
  have hcb := Ne.symm hbc
  cases left <;> cases right <;> cases cut <;>
    simp [labelledTriple, labelledPartition, agreement, partitionCheck, leaves,
      restrictionAgrees, restrict, sameShape, pairwiseEmbeddings,
      disjointVertices, minimalVertices, rootedSpan, prependSide,
      hab, hac, hbc, hba, hca, hcb]

theorem full_triple_agrees_iff (a b c : Nat)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (left right : TripleShape) :
    agreement (labelledTriple a b c left) (labelledTriple a b c right)
      [[a, b, c]] = decide (left = right) := by
  have hba := Ne.symm hab
  have hca := Ne.symm hac
  have hcb := Ne.symm hbc
  cases left <;> cases right <;>
    simp [labelledTriple, agreement, partitionCheck, leaves,
      restrictionAgrees, restrict, sameShape, pairwiseEmbeddings,
      hab, hac, hbc, hba, hca, hcb]

theorem leaves_positive (t : Tree) : 0 < (leaves t).length := by
  induction t with
  | leaf x => simp [leaves]
  | node l r hl hr => simp [leaves]; omega

theorem one_leaf_structure (t : Tree) (h : (leaves t).length = 1) :
    ∃ a, t = .leaf a := by
  cases t with
  | leaf a => exact ⟨a, rfl⟩
  | node l r =>
      have hl := leaves_positive l
      have hr := leaves_positive r
      simp [leaves] at h
      omega

theorem two_leaf_structure (t : Tree) (h : (leaves t).length = 2) :
    ∃ a b, t = .node (.leaf a) (.leaf b) := by
  cases t with
  | leaf a => simp [leaves] at h
  | node l r =>
      have hl := leaves_positive l
      have hr := leaves_positive r
      simp [leaves] at h
      rcases one_leaf_structure l (by omega) with ⟨a, ha⟩
      rcases one_leaf_structure r (by omega) with ⟨b, hb⟩
      exact ⟨a, b, by rw [ha, hb]⟩

theorem three_leaf_structure (t : Tree) (h : (leaves t).length = 3) :
    (∃ a b c, t = .node (.node (.leaf a) (.leaf b)) (.leaf c)) ∨
    (∃ a b c, t = .node (.leaf a) (.node (.leaf b) (.leaf c))) := by
  cases t with
  | leaf a => simp [leaves] at h
  | node l r =>
      have hl := leaves_positive l
      have hr := leaves_positive r
      simp [leaves] at h
      have hc : (leaves l).length = 1 ∨ (leaves l).length = 2 := by omega
      rcases hc with hc | hc
      · rcases one_leaf_structure l hc with ⟨a, ha⟩
        rcases two_leaf_structure r (by omega) with ⟨b, c, hb⟩
        exact Or.inr ⟨a, b, c, by rw [ha, hb]⟩
      · rcases two_leaf_structure l hc with ⟨a, b, ha⟩
        rcases one_leaf_structure r (by omega) with ⟨c, hc⟩
        exact Or.inl ⟨a, b, c, by rw [ha, hc]⟩

#print axioms canonical_proper_triples
#print axioms proper_triple_valid
#print axioms bad_full_triple_rejected
#print axioms arbitrary_label_proper_triples
#print axioms full_triple_agrees_iff
#print axioms leaves_positive
#print axioms one_leaf_structure
#print axioms two_leaf_structure
#print axioms three_leaf_structure
end TripleSemanticControls
