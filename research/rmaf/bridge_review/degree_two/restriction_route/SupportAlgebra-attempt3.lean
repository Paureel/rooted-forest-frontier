import RestrictionTransport
namespace RestrictionRoute
open RMAF

def Apart (xs ys : List Vertex) : Prop := ∀ v ∈ xs, v ∉ ys

theorem apart_iff_disjointVertices (xs ys : List Vertex) :
    Apart xs ys ↔ disjointVertices xs ys = true := by
  simp [Apart, disjointVertices, List.all_eq_true]

theorem apart_symm (xs ys : List Vertex) : Apart xs ys ↔ Apart ys xs := by
  constructor <;> intro h v hv w <;> exact h v w hv

@[simp] theorem apart_nil_left (xs : List Vertex) : Apart [] xs := by simp [Apart]
@[simp] theorem apart_nil_right (xs : List Vertex) : Apart xs [] := by simp [Apart]

theorem apart_append_left (xs ys zs : List Vertex) :
    Apart (xs ++ ys) zs ↔ Apart xs zs ∧ Apart ys zs := by
  simp [Apart, List.mem_append, or_imp, forall_and]

theorem apart_append_right (xs ys zs : List Vertex) :
    Apart xs (ys ++ zs) ↔ Apart xs ys ∧ Apart xs zs := by
  simp [Apart, List.mem_append, not_or, forall_and]

@[simp] theorem apart_prepend_same (side : Bool) (xs ys : List Vertex) :
    Apart (prependSide side xs) (prependSide side ys) ↔ Apart xs ys := by
  simp [Apart, prependSide]
  constructor
  · intro h v hv hy
    exact h v hv v hy rfl
  · intro h v hv w hw heq
    subst w
    exact h v hv hw

@[simp] theorem apart_prepend_opposite (side : Bool) (xs ys : List Vertex) :
    Apart (prependSide side xs) (prependSide (!side) ys) := by
  cases side <;> simp [Apart, prependSide]

@[simp] theorem apart_root_prepend (side : Bool) (xs : List Vertex) :
    Apart [[]] (prependSide side xs) := by simp [Apart, prependSide]
@[simp] theorem apart_prepend_root (side : Bool) (xs : List Vertex) :
    Apart (prependSide side xs) [[]] := by simp [Apart, prependSide]

@[simp] theorem apart_prepend_false_true (xs ys : List Vertex) :
    Apart (prependSide false xs) (prependSide true ys) := apart_prepend_opposite false xs ys
@[simp] theorem apart_prepend_true_false (xs ys : List Vertex) :
    Apart (prependSide true xs) (prependSide false ys) := apart_prepend_opposite true xs ys
@[simp] theorem apart_root_root : ¬ Apart [[]] [[]] := by simp [Apart]

/-- A shell keeps a Boolean root and two child support lists. -/
def shell (root : Bool) (left right : List Vertex) : List Vertex :=
  (if root then [[]] else []) ++ prependSide false left ++ prependSide true right

theorem apart_shell (r s : Bool) (a b c d : List Vertex) :
    Apart (shell r a b) (shell s c d) ↔
    (r = true → s = false) ∧ Apart a c ∧ Apart b d := by
  cases r <;> cases s <;>
    simp [shell, apart_append_left, apart_append_right, and_assoc]

end RestrictionRoute
