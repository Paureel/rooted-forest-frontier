-- Own path/subtree prefix facts, proved from constructors and list definitions.
import BranchGeometry34
open RMAF Universal233 Universal233.CherryBranching VertexGeometry SourceBoundary
namespace HighChildren
theorem prefix_dropLast_strict (p q : List Bool) (h : p <+: q) (hne : p≠q) :
    p <+: q.dropLast := by
  obtain ⟨tail,rfl⟩ := h
  cases tail with
  | nil => exact False.elim (hne (List.append_nil p).symm)
  | cons s tail =>
    rw [List.dropLast_append_cons]
    exact List.prefix_append p _
theorem prefix_comparable (p q r : List Bool) (hp : p <+: r) (hq : q <+: r) :
    p <+: q ∨ q <+: p := by
  induction p generalizing q r with
  | nil => exact Or.inl List.nil_prefix
  | cons s p ih =>
    cases q with
    | nil => exact Or.inr List.nil_prefix
    | cons t q =>
      cases r with
      | nil => exact False.elim (by simpa only [prefix_nil_iff,List.cons_ne_nil] using hp)
      | cons u r =>
        have h1 := (cons_prefix_iff s u p r).mp hp
        have h2 := (cons_prefix_iff t u q r).mp hq
        have he : s=t := h1.1.trans h2.1.symm
        subst t
        rcases ih q r h1.2 h2.2 with h | h
        · exact Or.inl (cons_prefix s h)
        · exact Or.inr (cons_prefix s h)
theorem path_prefix_endpoint {w a b : List Bool} (h : PathAt w a b)
    (v : List Bool) (hv : v <+: w) : v <+: a ∨ v <+: b := by
  induction h generalizing v with
  | endpointL a b => exact Or.inl hv
  | endpointR a b => exact Or.inr hv
  | fork a b =>
    have he := (prefix_nil_iff v).mp hv
    subst v
    exact Or.inl List.nil_prefix
  | fork' a b =>
    have he := (prefix_nil_iff v).mp hv
    subst v
    exact Or.inl List.nil_prefix
  | @down s w a b h ih =>
    cases v with
    | nil => exact Or.inl List.nil_prefix
    | cons t v =>
      have hh := (cons_prefix_iff t s v w).mp hv
      have he := hh.1
      subst t
      rcases ih v hh.2 with ha | hb
      · exact Or.inl (cons_prefix s ha)
      · exact Or.inr (cons_prefix s hb)
  | @leftLeg s w a h ih =>
    cases v with
    | nil => exact Or.inl List.nil_prefix
    | cons t v =>
      have hh := (cons_prefix_iff t s v w).mp hv
      have he := hh.1
      subst t
      rcases ih v hh.2 with ha | hb
      · exact Or.inl (cons_prefix s ha)
      · have he := (prefix_nil_iff v).mp hb
        subst v
        exact Or.inl (cons_prefix s List.nil_prefix)
  | @rightLeg s w b h ih =>
    cases v with
    | nil => exact Or.inl List.nil_prefix
    | cons t v =>
      have hh := (cons_prefix_iff t s v w).mp hv
      have he := hh.1
      subst t
      rcases ih v hh.2 with ha | hb
      · have he := (prefix_nil_iff v).mp ha
        subst v
        exact Or.inr (cons_prefix s List.nil_prefix)
      · exact Or.inr (cons_prefix s hb)
  | @crossLeft s w a b h ih =>
    cases v with
    | nil => exact Or.inl List.nil_prefix
    | cons t v =>
      have hh := (cons_prefix_iff t s v w).mp hv
      have he := hh.1
      subst t
      rcases ih v hh.2 with ha | hb
      · exact Or.inl (cons_prefix s ha)
      · have he := (prefix_nil_iff v).mp hb
        subst v
        exact Or.inl (cons_prefix s List.nil_prefix)
  | @crossRight s w a b h ih =>
    cases v with
    | nil => exact Or.inl List.nil_prefix
    | cons t v =>
      have hh := (cons_prefix_iff t s v w).mp hv
      have he := hh.1
      subst t
      rcases ih v hh.2 with ha | hb
      · have he := (prefix_nil_iff v).mp ha
        subst v
        exact Or.inr (cons_prefix s List.nil_prefix)
      · exact Or.inr (cons_prefix s hb)
theorem cuts_antichain (S : Tree) (a b : Nat) (v w : List Bool)
    (hv : v∈cuts S a b) (hw : w∈cuts S a b) (hp : v <+: w) : v=w := by
  apply Classical.byContradiction
  intro hne
  have hpre := prefix_dropLast_strict v w hp hne
  have hcV := cut_boundary S a b v hv
  have hcW := cut_boundary S a b w hw
  have hpath := child_parent_path v w.dropLast hpre
  have hV := (minimalVertices_correct [a,b] S v.dropLast).mp hcV.1
  have hW := (minimalVertices_correct [a,b] S w.dropLast).mp hcW.1
  exact hcV.2 ((minimalVertices_correct [a,b] S v).mpr
    (hull_convex (selectedLeaves [a,b] S) v v.dropLast w.dropLast hV hW hpath))
end HighChildren
