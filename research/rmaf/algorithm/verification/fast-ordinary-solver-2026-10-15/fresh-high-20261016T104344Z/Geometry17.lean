-- Own primitive span geometry. Not the universal dichotomy.
import Geometry15
open RMAF Universal233
namespace OwnHigh
theorem subtree_labels_subset (T U : Tree) (p : Vertex)
    (hp : CoreGraph.subtree T p = some U) : ∀ x ∈ leaves U, x ∈ leaves T := by
  induction p generalizing T with
  | nil =>
    simp [CoreGraph.subtree] at hp
    subst U
    exact fun _ hx => hx
  | cons side p ih =>
    cases T with
    | leaf x => simp [CoreGraph.subtree] at hp
    | node l r =>
      cases side with
      | false =>
        simp only [CoreGraph.subtree, Bool.false_eq_true, ↓reduceIte] at hp
        exact fun x hx => List.mem_append.mpr (.inl (ih l hp x hx))
      | true =>
        simp only [CoreGraph.subtree, ↓reduceIte] at hp
        exact fun x hx => List.mem_append.mpr (.inr (ih r hp x hx))
theorem cherry_a_mem (T : Tree) (p : Vertex) (a b : Nat)
    (hc : CoreGraph.CherryAt T p a b) : a ∈ leaves T := by
  exact subtree_labels_subset T (.node (.leaf a) (.leaf b)) p hc a (by simp [leaves])
theorem span_empty_iff (P : List Nat) (T : Tree) :
    rootedSpan P T = [] ↔ ∀ x ∈ leaves T, x ∉ P := by
  induction T with
  | leaf x => simp [rootedSpan, leaves, List.contains_iff_mem]
  | node l r ihl ihr =>
    simp [rootedSpan, leaves, Bool.and_eq_true, List.isEmpty_iff, ihl, ihr,
      List.mem_append, or_imp, forall_and]
theorem span_nonempty (P : List Nat) (T : Tree) (a : Nat)
    (ha : a ∈ leaves T) (hp : a ∈ P) : (rootedSpan P T).isEmpty = false := by
  have hn : rootedSpan P T ≠ [] := by
    intro h
    exact (span_empty_iff P T).mp h a ha hp
  exact Bool.eq_false_iff.mpr (fun h => hn (List.isEmpty_iff.mp h))
theorem cherry_in_rootedSpan (T : Tree) (p : Vertex) (a b : Nat) (P : List Nat)
    (hc : CoreGraph.CherryAt T p a b) (ha : a ∈ P) : p ∈ rootedSpan P T := by
  induction p generalizing T with
  | nil =>
    have he : T = .node (.leaf a) (.leaf b) := by
      simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
    subst T
    simp [rootedSpan, List.contains_iff_mem, ha]
  | cons side p ih =>
    cases T with
    | leaf x => simp [CoreGraph.CherryAt, CoreGraph.subtree] at hc
    | node l r =>
      cases side with
      | false =>
        have hcl : CoreGraph.CherryAt l p a b := by
          simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
        have hne := span_nonempty P l a (cherry_a_mem l p a b hcl) ha
        have hm := ih l hcl
        simpa [rootedSpan, hne, prependSide] using (Or.inl hm : p ∈ rootedSpan P l ∨ false)
      | true =>
        have hcr : CoreGraph.CherryAt r p a b := by
          simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
        have hne := span_nonempty P r a (cherry_a_mem r p a b hcr) ha
        have hm := ih r hcr
        simp [rootedSpan, hne, prependSide, hm]
end OwnHigh
