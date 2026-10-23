import OriginalEdges
open RootSafeOriginalEdges

example : normalize [4,5,6] (fun e : Nat => e == 4 || e == 6 || e == 7) none = [5] := by decide
example : normalize [3,4] (fun e : Nat => e == 3 || e == 4) (some 2) = [2] := by decide
example : normalize [2,3,4] (fun e : Nat => e == 3 || e == 4) (some 2) = [2] := by decide

def inc (e : Fin 3) (u v : Fin 4) : Prop :=
  (e = 0 ∧ ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0))) ∨
  (e = 1 ∧ ((u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0))) ∨
  (e = 2 ∧ ((u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0)))
instance (e : Fin 3) (u v : Fin 4) : Decidable (inc e u v) := by unfold inc; infer_instance

def pathEdge (e : Fin 3) : Bool := e == 0 || e == 1

theorem root_corridor_control (v : Fin 4)
    (h : Walk inc (fun e => e ∉ normalize [0,1,2] pathEdge none) 0 v) : v ≠ 3 := by
  apply normalized_component_isolated inc [0,1,2] [2] pathEdge none
    (fun x : Fin 4 => x ≠ 3) (by decide) (by decide) ?_ (by decide) h
  intro e u v hi hu hv
  have boundary : ∀ (e : Fin 3) (u v : Fin 4), inc e u v → u ≠ 3 → ¬ v ≠ 3 → e ∈ ([2] : List (Fin 3)) := by decide
  exact Or.inl (boundary e u v hi hu hv)

#print axioms root_corridor_control
