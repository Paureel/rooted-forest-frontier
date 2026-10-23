import OriginalEdges

/-! Original-edge IDs are child vertices. Parent ranks strictly increase away
from the root. No forest-isomorphism or suppression theorem is imported. -/
namespace RootSafeOriginalEdges
namespace RootedPaths

variable {Vertex : Type} [DecidableEq Vertex]

def incidence (parent : Vertex → Option Vertex) (edge u v : Vertex) : Prop :=
  (parent edge = some u ∧ v = edge) ∨ (parent edge = some v ∧ u = edge)

omit [DecidableEq Vertex] in
theorem incidence_symmetric (parent : Vertex → Option Vertex) :
    ∀ e u v, incidence parent e u v → incidence parent e v u := by
  intro e u v h
  exact h.elim Or.inr Or.inl

inductive DownPath (parent : Vertex → Option Vertex) :
    Vertex → Vertex → List Vertex → Prop where
  | refl (v : Vertex) : DownPath parent v v []
  | step {u child v : Vertex} {edges : List Vertex} :
      parent child = some u → DownPath parent child v edges →
      DownPath parent u v (child :: edges)

namespace DownPath

omit [DecidableEq Vertex] in
theorem edges_deeper {parent : Vertex → Option Vertex}
    (depth : Vertex → Nat)
    (parent_depth : ∀ u v, parent v = some u → depth u < depth v)
    {u v : Vertex} {edges : List Vertex} (h : DownPath parent u v edges) :
    ∀ e ∈ edges, depth u < depth e := by
  induction h with
  | refl _ => intro e he; simp at he
  | @step u child v edges hp _ ih =>
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e; exact parent_depth u child hp
    · have h₁ := parent_depth u child hp
      have h₂ := ih e he
      omega

omit [DecidableEq Vertex] in
theorem start_not_mem {parent : Vertex → Option Vertex}
    (depth : Vertex → Nat)
    (parent_depth : ∀ u v, parent v = some u → depth u < depth v)
    {u v : Vertex} {edges : List Vertex} (h : DownPath parent u v edges) :
    u ∉ edges := by
  intro hu
  have hh := h.edges_deeper depth parent_depth u hu
  omega

omit [DecidableEq Vertex] in
theorem to_walk {parent : Vertex → Option Vertex} {live : Vertex → Prop}
    {u v : Vertex} {edges : List Vertex} (h : DownPath parent u v edges)
    (allowed : ∀ e ∈ edges, live e) : Walk (incidence parent) live u v := by
  induction h with
  | refl w => exact .refl w
  | @step u child v edges hp _ ih =>
    apply Walk.step (Or.inl ⟨hp, rfl⟩) (allowed child (by simp))
    exact ih (fun e he => allowed e (by simp [he]))
end DownPath

/-- The incoming edge of the common ancestor is its original child-vertex ID.
It is absent if the common ancestor is a component root. -/
def incoming (parent : Vertex → Option Vertex) (u : Vertex) : Option Vertex :=
  (parent u).map (fun _ => u)

omit [DecidableEq Vertex] in
theorem incoming_id {parent : Vertex → Option Vertex} {u e : Vertex}
    (h : incoming parent u = some e) : e = u := by
  unfold incoming at h
  cases hp : parent u with
  | none => simp [hp] at h
  | some p => simpa [hp] using h.symm

/-- In any ranked parent forest, an available incoming edge of a common
ancestor lies outside both downward path arms. No LCA-parent existence is
assumed at a component root. -/
theorem incoming_off_path {parent : Vertex → Option Vertex}
    (depth : Vertex → Nat)
    (parent_depth : ∀ u v, parent v = some u → depth u < depth v)
    {u a c : Vertex} {left right : List Vertex}
    (ha : DownPath parent u a left) (hc : DownPath parent u c right) :
    ∀ e, incoming parent u = some e → (left ++ right).contains e = false := by
  intro e he
  have hid := incoming_id he
  subst e
  have hleft := ha.start_not_mem depth parent_depth
  have hright := hc.start_not_mem depth parent_depth
  simp [List.contains_eq_mem, List.mem_append, hleft, hright]

/-- Root-safe restoration reconnects the endpoints along the actual original
parent edges. The optional parent edge is derived from the parent map. -/
theorem normalized_rooted_path_connected
    (parent : Vertex → Option Vertex) (depth : Vertex → Nat)
    (parent_depth : ∀ u v, parent v = some u → depth u < depth v)
    (cuts : List Vertex) {u a c : Vertex} {left right : List Vertex}
    (ha : DownPath parent u a left) (hc : DownPath parent u c right) :
    Walk (incidence parent)
      (fun e => e ∉ normalize cuts (fun e => (left ++ right).contains e)
        (incoming parent u)) a c := by
  apply endpoint_path_restored (incidence parent) cuts
    (fun e => (left ++ right).contains e) (incoming parent u)
    (incoming_off_path depth parent_depth ha hc)
  have wa : Walk (incidence parent)
      (fun e => (left ++ right).contains e = true) u a :=
    ha.to_walk (fun e he => by simp [List.contains_eq_mem, he])
  have wc : Walk (incidence parent)
      (fun e => (left ++ right).contains e = true) u c :=
    hc.to_walk (fun e he => by simp [List.contains_eq_mem, he])
  exact (wa.symm (incidence_symmetric parent)).trans wc

#print axioms incidence_symmetric
#print axioms DownPath.edges_deeper
#print axioms DownPath.start_not_mem
#print axioms DownPath.to_walk
#print axioms incoming_id
#print axioms incoming_off_path
#print axioms normalized_rooted_path_connected
end RootedPaths
end RootSafeOriginalEdges
