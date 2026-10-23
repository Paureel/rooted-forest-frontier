import RootedPaths
open RootSafeOriginalEdges RootSafeOriginalEdges.RootedPaths

def par (v : Fin 4) : Option (Fin 4) := if v = 0 then none else some 0

theorem parent_rank : ∀ u v, par v = some u → u.val < v.val := by decide
example : incoming par 0 = none := by decide
example : normalize [1,2,3] (fun e : Fin 4 => ([1,2] : List (Fin 4)).contains e)
    (incoming par 0) = [3] := by decide

theorem rooted_reconnection_control : Walk (incidence par)
    (fun e => e ∉ normalize [1,2,3]
      (fun e => ([1,2] : List (Fin 4)).contains e) (incoming par 0)) 1 2 := by
  have left : DownPath par 0 1 [1] := .step (by decide) (.refl 1)
  have right : DownPath par 0 2 [2] := .step (by decide) (.refl 2)
  exact normalized_rooted_path_connected par Fin.val parent_rank [1,2,3] left right

#print axioms rooted_reconnection_control
