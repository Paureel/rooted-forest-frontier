import RMAF

/-! Intentionally false expectations. This file MUST fail to compile twice.
It is a destructive comparator control, not an imported proof artifact. -/
namespace PrefixRouteNegative
open RMAF

def sameMembers (xs ys : List Vertex) : Bool :=
  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)

def four : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))

-- Missing [false] separates [false,false] from the other path vertices.
theorem wrong_missing_path :
    sameMembers (minimalVertices [0, 2] four)
      [[], [false,false], [true], [true,false]] = true := by decide

-- Selected label 9 has no leaf occurrence; epsilon must not be retained.
theorem wrong_absent_label :
    sameMembers (minimalVertices [9] four) [[]] = true := by decide
end PrefixRouteNegative
