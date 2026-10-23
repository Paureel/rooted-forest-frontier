import ParentColors
import Branches

/-! One-shot actual-parent graph invariant. The only graph witness is an ordinary
source partition with connected disjoint supports, constructed from source
checks and propagated through actual contraction and leaf erasure. -/
namespace Universal233.KeptParent
open RMAF CoreGraph CoreProgram Integration Assembly

def ResidueOwners (t : GTree) (P : SourcePartition (skeleton t)) : Prop :=
  ∀ v c, LeafAt (skeleton t) v c → P.owner v = c % 3

def ResidueSource (t : GTree) : Prop :=
  ∃ P : SourcePartition (skeleton t), ResidueOwners t P

def UniformResidue (t : GTree) (k : Nat) : Prop :=
  ∀ v c, LeafAt (skeleton t) v c → c % 3 = k % 3 → c = k

theorem residue_monochromatic {t : GTree} {P : SourcePartition (skeleton t)}
    (h : ResidueOwners t P) : Monochromatic P (fun c => c % 3) := by
  intro u v x y hu hv ho
  exact (h u x hu).symm.trans (ho.trans (h v y hv))

theorem contraction_residue {t u p c} (h : GContract t u p c)
    (P : SourcePartition (skeleton t)) (hp : ResidueOwners t P) : ResidueSource u := by
  have hc := gcontract_graph h
  have hs : P.owner (p ++ [false]) = P.owner (p ++ [true]) :=
    (hp _ c (cherry_left (contraction_cherry hc))).trans
      (hp _ c (cherry_right (contraction_cherry hc))).symm
  refine ⟨contractPartition hc P hs,?_⟩
  intro v d hv
  rcases contraction_terminal hc v d hv with ⟨hvp,hdc⟩ | hold
  · subst v; subst d
    change contractOwner P p p = c % 3
    simpa [contractOwner] using hp _ c (cherry_left (contraction_cherry hc))
  · have hn := cherry_parent_not_terminal (contraction_cherry hc) hold
    change contractOwner P p v = d % 3
    simpa [contractOwner,hn] using hp v d hold

theorem gcontracts_residue {t u} (h : GContracts t u) (hp : ResidueSource t) :
    ResidueSource u := by
  induction h with
  | refl => exact hp
  | step hr hs ih => obtain ⟨P,hP⟩ := hp; exact ih (contraction_residue hr P hP)

theorem normalize_residue (t : GTree) (hp : ResidueSource t) :
    ResidueSource (normalize t) := gcontracts_residue (normalize_gcontracts t) hp

theorem contraction_uniform {t u p c} (h : GContract t u p c) (k : Nat)
    (hu : UniformResidue t k) : UniformResidue u k := by
  intro v d hv hd
  have hc := gcontract_graph h
  rcases contraction_terminal hc v d hv with ⟨hvp,hdc⟩ | hold
  · subst v; subst d
    exact hu _ c (cherry_left (contraction_cherry hc)) hd
  · exact hu _ d hold hd

theorem gcontracts_uniform {t u} (h : GContracts t u) (k : Nat)
    (hu : UniformResidue t k) : UniformResidue u k := by
  induction h with
  | refl => exact hu
  | step hr hs ih => exact ih (contraction_uniform hr k hu)

theorem normalize_uniform (t : GTree) (k : Nat) (hu : UniformResidue t k) :
    UniformResidue (normalize t) k :=
  gcontracts_uniform (normalize_gcontracts t) k hu

theorem erasure_residue {t u v g} (h : GLeafErase t u v g) (hp : ResidueSource t) :
    ResidueSource u := by
  obtain ⟨P,hP⟩ := hp
  refine ⟨erasePartition (gLeafErase_graph h) P,?_⟩
  intro w c hw
  exact hP _ c (erasure_leaf (gLeafErase_graph h) w c hw)

theorem erasure_uniform {t u v g} (h : GLeafErase t u v g) (k : Nat)
    (hu : UniformResidue t k) : UniformResidue u k := by
  intro w c hw hc
  exact hu _ c (erasure_leaf (gLeafErase_graph h) w c hw) hc

theorem groups_nodup (t : GTree) (hn : (origins t).Nodup) : (groups t).Nodup := by
  induction t with
  | leaf g => simp [groups]
  | node p l r ihl ihr =>
    obtain ⟨_,hn⟩ := List.nodup_cons.1 hn
    obtain ⟨hl,hr,hd⟩ := List.nodup_append.1 hn
    apply List.nodup_append.2
    refine ⟨ihl hl,ihr hr,?_⟩
    intro a ha b hb he
    obtain ⟨v,hv⟩ := groupLeaf_of_groups_mem l a ha
    obtain ⟨w,hw⟩ := groupLeaf_of_groups_mem r b hb
    exact hd _ (groupLeaf_origin_mem l v a hv) _ (groupLeaf_origin_mem r w b hw)
      (congrArg Group.origin he)

theorem nodup_singleton {α : Type} {xs : List α} {a : α}
    (hn : xs.Nodup) (ha : a ∈ xs) (hu : ∀ b, b ∈ xs → b = a) : xs = [a] := by
  cases xs with
  | nil => simp at ha
  | cons b tail =>
    have hb := hu b (by simp)
    subst b
    cases tail with
    | nil => rfl
    | cons b tail =>
      have hb := hu b (by simp)
      subst b
      simp at hn

theorem singleton_color_filter {t : GTree} (hn : (origins t).Nodup)
    (P : SourcePartition (skeleton t)) (hp : ResidueOwners t P)
    {v : RMAF.Vertex} {g : Group} (hv : GroupLeafAt t v g) (hs : SingletonBlock P v) :
    ((groups t).filter (fun a => a.color == g.color)).length = 1 := by
  have hg := groupLeaf_mem_groups t v g hv
  have he : (groups t).filter (fun a => a.color == g.color) = [g] := by
    apply nodup_singleton ((groups_nodup t hn).filter _) (by simp [hg])
    intro a ha
    have hmem := (List.mem_filter.1 ha).1
    have hc : a.color = g.color := by simpa using (List.mem_filter.1 ha).2
    obtain ⟨w,hw⟩ := groupLeaf_of_groups_mem t a hmem
    have ho : P.owner w = P.owner v := by
      rw [hp w a.color (groupLeaf_skeleton t w a hw),hp v g.color (groupLeaf_skeleton t v g hv),hc]
    have hwv := hs w a.color (groupLeaf_skeleton t w a hw) ho
    subst w
    exact Option.some.inj (hw.symm.trans hv)
  simp [he]

theorem choose_two_no_unique (t : GTree) (a b : Group) (hc : choose t = .two a b)
    (g : Group) (hg : g ∈ groups t) :
    ((groups t).filter (fun h => h.color == g.color)).length ≠ 1 := by
  cases hgs : groups t with
  | nil => simp [hgs] at hg
  | cons first rest =>
    simp only [choose,hgs] at hc
    split at hc
    next => cases hc
    next =>
      cases hf : (first :: rest).find? (fun g => ((first :: rest).filter (fun h => h.color == g.color)).length == 1) with
      | some g => simp [hf] at hc
      | none =>
        have hh := List.find?_eq_none.1 hf g (by simpa [hgs] using hg)
        intro he
        simp [he] at hh

/-- Every two-child branch stays within one ORIGINAL parent residue. It is not
merely the existence of one safe branch: both offered groups share the parent. -/
theorem choose_two_same_parent (t : GTree) (hn : (origins t).Nodup)
    (hp : ResidueSource t) (a b : Group) (hc : choose t = .two a b) :
    a.color % 3 = b.color % 3 := by
  obtain ⟨P,hP⟩ := hp
  obtain ⟨p,hch,hne⟩ := choose_two_selected t a b hc
  apply Classical.byContradiction
  intro hmod
  have hs := mixed_cherry_singleton P (gcherry_graph hch) (fun c => c % 3)
    (residue_monochromatic hP) hmod
  rcases hs with hs | hs
  · have hf := singleton_color_filter hn P hP (gcherry_left hch) hs
    exact choose_two_no_unique t a b hc a
      (groupLeaf_mem_groups t _ a (gcherry_left hch)) hf
  · have hf := singleton_color_filter hn P hP (gcherry_right hch) hs
    exact choose_two_no_unique t a b hc b
      (groupLeaf_mem_groups t _ b (gcherry_right hch)) hf

/-- Constant local A or C can never be an offered mixed-cherry cut, on either
branch. This follows from actual graph supports and the exact chooser. -/
theorem choose_two_avoids_uniform (t : GTree) (hn : (origins t).Nodup)
    (hp : ResidueSource t) (k : Nat) (hu : UniformResidue t k)
    (a b : Group) (hc : choose t = .two a b) : a.color ≠ k ∧ b.color ≠ k := by
  have hm := choose_two_same_parent t hn hp a b hc
  obtain ⟨p,hch,hne⟩ := choose_two_selected t a b hc
  constructor
  · intro ha
    have hb : b.color = k := hu _ b.color
      (groupLeaf_skeleton t _ b (gcherry_right hch)) (by simpa [ha] using hm.symm)
    exact hne (ha.trans hb.symm)
  · intro hb
    have ha : a.color = k := hu _ a.color
      (groupLeaf_skeleton t _ a (gcherry_left hch)) (by simpa [hb] using hm)
    exact hne (ha.trans hb.symm)

end Universal233.KeptParent
