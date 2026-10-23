-- Own universal lower geometry from tree/path definitions; no domain theorem reuse.
import Ordinary
import ProperJobs
open RMAF Universal233
namespace OwnHigh
theorem subtree_nodup (T U : Tree) (p : Vertex)
    (ht : (leaves T).Nodup) (hp : CoreGraph.subtree T p = some U) :
    (leaves U).Nodup := by
  induction p generalizing T with
  | nil =>
    simp [CoreGraph.subtree] at hp
    subst U
    exact ht
  | cons side p ih =>
    cases T with
    | leaf x => simp [CoreGraph.subtree] at hp
    | node l r =>
      simp only [leaves] at ht
      cases side with
      | false =>
        simp only [CoreGraph.subtree, Bool.false_eq_true, ↓reduceIte] at hp
        exact ih l (List.nodup_append.mp ht).1 hp
      | true =>
        simp only [CoreGraph.subtree, ↓reduceIte] at hp
        exact ih r (List.nodup_append.mp ht).2.1 hp
theorem cherry_distinct (T S : Tree) (p : Vertex) (a b : Nat)
    (hproper : DepthOne.proper T S = true) (hc : CoreGraph.CherryAt T p a b) : a ≠ b := by
  have ht : (leaves T).Nodup := by
    simpa only [DepthOne.proper, Bool.and_eq_true, decide_eq_true_eq] using (And.left (Bool.and_eq_true.mp hproper)).1
  have hn := subtree_nodup T (.node (.leaf a) (.leaf b)) p ht hc
  simpa [leaves] using hn
end OwnHigh
