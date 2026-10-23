import IndexRoute
open TripleDP.CostRoute.IndexRoute
-- singleton
example : enumeration (["o"] : List String) (["o"] : List String) "o" "o" = [Joined.boundary] := by decide
example : (enumeration (["o"] : List String) (["o"] : List String) "o" "o").length = 1 ∧ (closedEnumeration (["o"] : List String) (["o"] : List String) "o" "o").length = 0 := by decide
-- left-extra
example : enumeration (["o", "c"] : List String) (["o"] : List String) "o" "o" = [Joined.boundary, Joined.left ⟨"c", by decide⟩] := by decide
example : (enumeration (["o", "c"] : List String) (["o"] : List String) "o" "o").length = 2 ∧ (closedEnumeration (["o", "c"] : List String) (["o"] : List String) "o" "o").length = 1 := by decide
-- same-name-collision
example : enumeration (["o", "c"] : List String) (["o", "c"] : List String) "o" "o" = [Joined.boundary, Joined.left ⟨"c", by decide⟩, Joined.right ⟨"c", by decide⟩] := by decide
example : (enumeration (["o", "c"] : List String) (["o", "c"] : List String) "o" "o").length = 3 ∧ (closedEnumeration (["o", "c"] : List String) (["o", "c"] : List String) "o" "o").length = 2 := by decide
-- asymmetric
example : enumeration (["o", "a", "c"] : List String) (["o", "e"] : List String) "o" "o" = [Joined.boundary, Joined.left ⟨"a", by decide⟩, Joined.left ⟨"c", by decide⟩, Joined.right ⟨"e", by decide⟩] := by decide
example : (enumeration (["o", "a", "c"] : List String) (["o", "e"] : List String) "o" "o").length = 4 ∧ (closedEnumeration (["o", "a", "c"] : List String) (["o", "e"] : List String) "o" "o").length = 3 := by decide
-- boundary-middle
example : enumeration (["a", "o", "b"] : List String) (["e", "o"] : List String) "o" "o" = [Joined.boundary, Joined.left ⟨"a", by decide⟩, Joined.left ⟨"b", by decide⟩, Joined.right ⟨"e", by decide⟩] := by decide
example : (enumeration (["a", "o", "b"] : List String) (["e", "o"] : List String) "o" "o").length = 4 ∧ (closedEnumeration (["a", "o", "b"] : List String) (["e", "o"] : List String) "o" "o").length = 3 := by decide
