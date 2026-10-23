-- Own address/path geometry, using PathAt constructors only.
import SourceBasics05
open RMAF Universal233 VertexGeometry
namespace SourceBoundary
theorem cons_prefix_iff (s t : Bool) (p q : List Bool) :
    (s::p) <+: (t::q) ↔ s=t ∧ p <+: q := by
  constructor
  · rintro ⟨tail,h⟩
    have hh := List.cons.inj h
    exact ⟨hh.1,tail,hh.2⟩
  · rintro ⟨rfl,tail,h⟩
    exact ⟨tail,congrArg (List.cons s) h⟩
theorem prefix_nil_iff (p : List Bool) : p <+: [] ↔ p=[] := by
  cases p <;> simp [List.IsPrefix]
theorem cons_prefix (s : Bool) {p q : List Bool} (h : p <+: q) : (s::p) <+: (s::q) :=
  (cons_prefix_iff s s p q).mpr ⟨rfl,h⟩
theorem path_prefix_closed {v a b : List Bool} (h : PathAt v a b)
    (p : List Bool) (ha : p <+: a) (hb : p <+: b) : p <+: v := by
  induction h generalizing p with
  | endpointL a b => exact ha
  | endpointR a b => exact hb
  | fork a b =>
    cases p with
    | nil => exact List.nil_prefix
    | cons s p =>
      have h0 := ((cons_prefix_iff s false p a).mp ha).1
      have h1 := ((cons_prefix_iff s true p b).mp hb).1
      exact False.elim (Bool.noConfusion (h0.symm.trans h1))
  | fork' a b =>
    cases p with
    | nil => exact List.nil_prefix
    | cons s p =>
      have h1 := ((cons_prefix_iff s true p a).mp ha).1
      have h0 := ((cons_prefix_iff s false p b).mp hb).1
      exact False.elim (Bool.noConfusion (h0.symm.trans h1))
  | @down s v a b h ih =>
    cases p with
    | nil => exact List.nil_prefix
    | cons t p =>
      have ha' := (cons_prefix_iff t s p a).mp ha
      have hb' := (cons_prefix_iff t s p b).mp hb
      have he := ha'.1
      subst t
      exact cons_prefix s (ih p ha'.2 hb'.2)
  | @leftLeg s v a h ih =>
    have he := (prefix_nil_iff p).mp hb
    subst p
    exact List.nil_prefix
  | @rightLeg s v b h ih =>
    have he := (prefix_nil_iff p).mp ha
    subst p
    exact List.nil_prefix
  | @crossLeft s v a b h ih =>
    cases p with
    | nil => exact List.nil_prefix
    | cons t p =>
      have h1 := ((cons_prefix_iff t s p a).mp ha).1
      have h2 := ((cons_prefix_iff t (!s) p b).mp hb).1
      have he : s = !s := h1.symm.trans h2
      cases s <;> simp at he
  | @crossRight s v a b h ih =>
    cases p with
    | nil => exact List.nil_prefix
    | cons t p =>
      have h1 := ((cons_prefix_iff t (!s) p a).mp ha).1
      have h2 := ((cons_prefix_iff t s p b).mp hb).1
      have he : s = !s := h2.symm.trans h1
      cases s <;> simp at he
theorem prefix_root_path (p a : List Bool) (h : p <+: a) : PathAt p a [] := by
  induction p generalizing a with
  | nil => exact PathAt.endpointR a []
  | cons s p ih =>
    cases a with
    | nil => exact False.elim (by simpa [List.IsPrefix] using h)
    | cons t a =>
      have hh := (cons_prefix_iff s t p a).mp h
      have he := hh.1
      subst t
      exact PathAt.leftLeg s (ih a hh.2)
theorem prefix_path (p : List Bool) {v a b : List Bool} (h : PathAt v a b) :
    PathAt (p++v) (p++a) (p++b) := by
  induction p with
  | nil => exact h
  | cons s p ih => exact PathAt.down s ih
theorem parent_separates (p a b : List Bool) (ha : p <+: a) (hb : ¬ p <+: b) :
    PathAt p.dropLast a b := by
  induction p generalizing a b with
  | nil => exact False.elim (hb List.nil_prefix)
  | cons s p ih =>
    obtain ⟨tail,rfl⟩ := ha
    cases p with
    | nil =>
      cases b with
      | nil => exact PathAt.endpointR _ []
      | cons t b =>
        cases s <;> cases t
        · exact False.elim (hb (cons_prefix false List.nil_prefix))
        · exact PathAt.fork tail b
        · exact PathAt.fork' tail b
        · exact False.elim (hb (cons_prefix true List.nil_prefix))
    | cons t p =>
      have hp : (t::p).dropLast <+: (t::p)++tail :=
        (List.dropLast_prefix (t::p)).trans (List.prefix_append (t::p) tail)
      have hroot := prefix_root_path (t::p).dropLast ((t::p)++tail) hp
      cases b with
      | nil => exact PathAt.leftLeg s hroot
      | cons u b =>
        cases s <;> cases u
        · have hb' : ¬ (t::p) <+: b := fun h => hb (cons_prefix false h)
          exact PathAt.down false (ih ((t::p)++tail) b (List.prefix_append _ _) hb')
        · exact PathAt.crossLeft false hroot
        · exact PathAt.crossLeft true hroot
        · have hb' : ¬ (t::p) <+: b := fun h => hb (cons_prefix true h)
          exact PathAt.down true (ih ((t::p)++tail) b (List.prefix_append _ _) hb')
end SourceBoundary
