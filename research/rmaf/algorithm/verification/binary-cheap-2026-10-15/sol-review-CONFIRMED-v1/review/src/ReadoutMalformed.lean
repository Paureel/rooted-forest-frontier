import IndependentReadout
open Lean Universal233 RMAF
namespace MalformedObserver
def S : Tree := (.node ((.node ((.node ((.node (.leaf 1) (.leaf 2))) (.leaf 3))) ((.node ((.node ((.node (.leaf 5) (.leaf 7))) (.leaf 9))) ((.node ((.node (.leaf 6) (.leaf 8))) (.leaf 10))))))) ((.node (.leaf 11) (.leaf 12))))
def T : Tree := (.node ((.node ((.node (.leaf 1) ((.node ((.node (.leaf 5) (.leaf 6))) ((.node (.leaf 7) (.leaf 8))))))) ((.node ((.node (.leaf 2) (.leaf 3))) ((.node (.leaf 9) (.leaf 10))))))) ((.node (.leaf 11) (.leaf 12))))
def A : List Nat := [1,2,3]
def B : List Nat := [5,6,7,8,9,10]
def swapped : Tree := (.node ((.node (.leaf 11) (.leaf 12))) ((.node ((.node ((.node (.leaf 1) (.leaf 2))) (.leaf 3))) ((.node ((.node ((.node (.leaf 5) (.leaf 7))) (.leaf 9))) ((.node ((.node (.leaf 6) (.leaf 8))) (.leaf 10))))))))
#eval IndependentReadout.emit (Json.mkObj [
 ("missing_label_selector",IndependentReadout.selector T (A++[999]) B),
 ("duplicate_parent_selector",IndependentReadout.selector T (A++[1]) B),
 ("child_order_same_rooted_topology",toJson (RMAF.sameShape S swapped)),
 ("suppressed_path",toJson (IndependentReadout.hull (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)) [0,2])),
 ("transported_parent_hulls",toJson ([[1,2,3],[5,6,7,8,9,10],[11,12]].map (IndependentReadout.hull swapped)))])
end MalformedObserver
