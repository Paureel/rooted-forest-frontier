import KeptGraph
import ValidPartition

/-! Literal recursion consumer. The intact membership predicate below is proved
from initial leaf membership and propagated by the actual operations; it is
never an assumed source-call preservation record. -/
namespace Universal233.KeptParent
open RMAF CoreGraph CoreProgram Integration CutRealization

def SameMembers (K A : List Nat) : Prop := ∀ x, x ∈ K ↔ x ∈ A

def Keeps (A : List Nat) (o : Output) : Prop :=
  ∃ K, K ∈ o.partition ∧ SameMembers K A

def HasDetached (A : List Nat) (d : List Group) : Prop :=
  ∃ g, g ∈ d ∧ SameMembers g.labels A

def CurrentLabels (A : List Nat) (color : Nat → Nat) (k : Nat) (t : GTree) : Prop :=
  ∀ x, x ∈ A ↔ x ∈ payload t ∧ color x = k

theorem attempt_detached (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (hf : ∀ t d c, HasDetached A d → ∀ o ∈ (f t d c).outputs, Keeps A o)
    (t d c g) (hd : HasDetached A d) (o) (ho : o ∈ (attempt f t d c g).outputs) :
    Keeps A o := by
  unfold attempt at ho
  split at ho
  · simp at ho
  · split at ho
    · simp at ho
    · split at ho
      · simp at ho
      · apply hf _ _ _ _ o ho
        obtain ⟨a,ha,hA⟩ := hd
        exact ⟨a,List.mem_cons_of_mem g ha,hA⟩

theorem step_detached (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (hf : ∀ t d c, HasDetached A d → ∀ o ∈ (f t d c).outputs, Keeps A o)
    (t d c) (hd : HasDetached A d) (o) (ho : o ∈ (step f t d c).outputs) :
    Keeps A o := by
  cases hc : choose (normalize t) with
  | finish =>
    have he : o = ⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels],c⟩ := by
      simpa [step,hc] using ho
    obtain ⟨g,hg,hA⟩ := hd
    refine ⟨g.labels,?_,hA⟩
    simp [he,List.mem_map.mpr ⟨g,hg,rfl⟩]
  | one g => exact attempt_detached f hf _ d c g hd o (by simpa [step,hc,prefixRoot] using ho)
  | two a b =>
    have he : o ∈ (attempt f (normalize t) d c a).outputs ∨
      o ∈ (attempt f (normalize t) d c b).outputs := by
      simpa [step,hc,prefixRoot,combine] using ho
    rcases he with he | he
    · exact attempt_detached f hf _ d c a hd o he
    · exact attempt_detached f hf _ d c b hd o he
  | refuse why => simp [step,hc] at ho

theorem run_detached (q : Nat) (t d c) (hd : HasDetached A d) (o)
    (ho : o ∈ (run q t d c).outputs) : Keeps A o := by
  induction q generalizing t d c o with
  | zero => exact step_detached _ (by intros; contradiction) t d c hd o ho
  | succ q ih => exact step_detached (run q) (by intros; exact ih _ _ _ ‹_› _ ‹_›) t d c hd o ho

theorem erasure_payload_membership {t u v g} (e : GLeafErase t u v g) (x : Nat) :
    x ∈ payload t ↔ x ∈ g.labels ∨ x ∈ payload u := by
  induction e with
  | rootLeft => simp [payload]
  | rootRight => simp [payload,or_comm]
  | left p r e ih => simpa only [payload,List.mem_append,ih,or_assoc]
  | right p l e ih => simpa only [payload,List.mem_append,ih,or_assoc,or_left_comm]

theorem erasure_current {t u v g} (e : GLeafErase t u v g) (color : Nat → Nat) (k : Nat)
    (hp : PureGroups color t) (hc : CurrentLabels A color k t) (hn : g.color ≠ k) :
    CurrentLabels A color k u := by
  intro x
  have he := erasure_payload_membership e x
  have hg := group_pure hp (SourceCoverage.gLeafErase_selected e)
  rw [hc x]
  constructor
  · rintro ⟨hx,hk⟩
    refine ⟨?_,hk⟩
    rcases he.1 hx with hx | hx
    · exact False.elim (hn ((hg x hx).symm.trans hk))
    · exact hx
  · rintro ⟨hx,hk⟩
    exact ⟨he.2 (Or.inr hx),hk⟩

theorem unique_group_current (t : GTree) (color : Nat → Nat) (k : Nat)
    (hp : PureGroups color t) (hA : CurrentLabels A color k t)
    (g : Group) (hg : g ∈ groups t) (hk : g.color = k)
    (hu : ((groups t).filter (fun a => a.color == g.color)).length = 1) :
    SameMembers g.labels A := by
  obtain ⟨v,hv⟩ := groupLeaf_of_groups_mem t g hg
  intro x
  constructor
  · intro hx
    apply (hA x).2
    refine ⟨?_,(group_pure hp hv x hx).trans hk⟩
    rw [payload_groups]
    exact List.mem_flatMap.mpr ⟨g,hg,hx⟩
  · intro hx
    obtain ⟨hx,hcol⟩ := (hA x).1 hx
    rw [payload_groups] at hx
    obtain ⟨a,ha,hxa⟩ := List.mem_flatMap.1 hx
    obtain ⟨w,hw⟩ := groupLeaf_of_groups_mem t a ha
    have hcolor : a.color = g.color := (group_pure hp hw x hxa).symm.trans (hcol.trans hk.symm)
    have he := unique_filter_group t g a hg ha hcolor hu
    simpa [he] using hxa

theorem finish_current (t : GTree) (color : Nat → Nat) (k : Nat)
    (hp : PureGroups color t) (hA : CurrentLabels A color k t) (ha : A ≠ [])
    (hc : choose t = .finish) : SameMembers ((groups t).flatMap Group.labels) A := by
  obtain ⟨col,hcol⟩ := choose_finish_uniform t hc
  have hck : col = k := by
    cases A with
    | nil => exact False.elim (ha rfl)
    | cons x xs =>
      have hx := (hA x).1 (by simp)
      rw [payload_groups] at hx
      obtain ⟨g,hg,hxg⟩ := List.mem_flatMap.1 hx.1
      obtain ⟨v,hv⟩ := groupLeaf_of_groups_mem t g hg
      exact (hcol g hg).symm.trans ((group_pure hp hv x hxg).symm.trans hx.2)
  intro x
  constructor
  · intro hx
    obtain ⟨g,hg,hxg⟩ := List.mem_flatMap.1 hx
    obtain ⟨v,hv⟩ := groupLeaf_of_groups_mem t g hg
    apply (hA x).2
    exact ⟨by rw [payload_groups]; exact List.mem_flatMap.2 ⟨g,hg,hxg⟩,
      (group_pure hp hv x hxg).trans ((hcol g hg).trans hck)⟩
  · intro hx
    have hh := (hA x).1 hx
    simpa only [payload_groups] using hh.1


theorem attempt_current (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (color : Nat → Nat) (k : Nat)
    (hf : ∀ t d c, (origins t).Nodup → ResidueSource t → UniformResidue t k →
      PureGroups color t → CurrentLabels A color k t → ∀ o ∈ (f t d c).outputs, Keeps A o)
    (hd : ∀ t d c, HasDetached A d → ∀ o ∈ (f t d c).outputs, Keeps A o)
    (t d c g) (hn : (origins t).Nodup) (hr : ResidueSource t)
    (hu : UniformResidue t k) (hp : PureGroups color t) (hA : CurrentLabels A color k t)
    (v : RMAF.Vertex) (hv : GroupLeafAt t v g) (hvr : v ≠ [])
    (hunique : g.color = k → ((groups t).filter (fun a => a.color == g.color)).length = 1)
    (o) (ho : o ∈ (attempt f t d c g).outputs) : Keeps A o := by
  unfold attempt at ho
  split at ho
  · simp at ho
  · split at ho
    · simp at ho
    · split at ho
      · simp at ho
      · rename_i next he
        obtain ⟨u,he',⟨e⟩⟩ := erase_leaf_realization t hn v g hv hvr
        have heu : u = next := Option.some.inj (he'.symm.trans he)
        subst u
        by_cases hk : g.color = k
        · have hsame := unique_group_current t color k hp hA g
            (groupLeaf_mem_groups t v g hv) hk (hunique hk)
          exact hd next (g :: d) (g.origin :: c) ⟨g,by simp,hsame⟩ o ho
        · exact hf next (g :: d) (g.origin :: c)
            (erase_origins_nodup t g.origin next he hn)
            (erasure_residue e hr) (erasure_uniform e k hu) (erase_pure e hp)
            (erasure_current e color k hp hA hk) o ho

theorem step_current (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (color : Nat → Nat) (k : Nat) (ha : A ≠ [])
    (hf : ∀ t d c, (origins t).Nodup → ResidueSource t → UniformResidue t k →
      PureGroups color t → CurrentLabels A color k t → ∀ o ∈ (f t d c).outputs, Keeps A o)
    (hd : ∀ t d c, HasDetached A d → ∀ o ∈ (f t d c).outputs, Keeps A o)
    (t d c) (hn : (origins t).Nodup) (hr : ResidueSource t)
    (hu : UniformResidue t k) (hp : PureGroups color t) (hA : CurrentLabels A color k t)
    (o) (ho : o ∈ (step f t d c).outputs) : Keeps A o := by
  have hnn := normalize_origins_nodup t hn
  have hrn := normalize_residue t hr
  have hun := normalize_uniform t k hu
  have hpn := normalize_pure color t hp
  have hAn : CurrentLabels A color k (normalize t) := by
    intro x; simpa only [normalize_payload] using hA x
  cases hc : choose (normalize t) with
  | finish =>
    have he : o = ⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels],c⟩ := by
      simpa [step,hc] using ho
    exact ⟨(groups (normalize t)).flatMap Group.labels,by simp [he],
      finish_current _ color k hpn hAn ha hc⟩
  | one g =>
    obtain ⟨hg,hgcount⟩ := choose_one_selected _ g hc
    obtain ⟨v,hv⟩ := groupLeaf_of_groups_mem _ g hg
    exact attempt_current f color k hf hd _ d c g hnn hrn hun hpn hAn v hv
      (choose_one_nonroot _ g hc v hv) (fun _ => hgcount) o
      (by simpa [step,hc,prefixRoot] using ho)
  | two a b =>
    have hav := choose_two_avoids_uniform _ hnn hrn k hun a b hc
    obtain ⟨p,hch,hne⟩ := choose_two_selected _ a b hc
    have he : o ∈ (attempt f (normalize t) d c a).outputs ∨
      o ∈ (attempt f (normalize t) d c b).outputs := by
      simpa [step,hc,prefixRoot,combine] using ho
    rcases he with he | he
    · exact attempt_current f color k hf hd _ d c a hnn hrn hun hpn hAn
        (p ++ [false]) (gcherry_left hch) (by simp)
        (fun hk => False.elim (hav.1 hk)) o he
    · exact attempt_current f color k hf hd _ d c b hnn hrn hun hpn hAn
        (p ++ [true]) (gcherry_right hch) (by simp)
        (fun hk => False.elim (hav.2 hk)) o he
  | refuse why => simp [step,hc] at ho

/-- Universal over every output of the actual bounded recursion, including q0.
All offered branches are handled separately. No existence-cover theorem occurs. -/
theorem run_keeps_current (q : Nat) (color : Nat → Nat) (k : Nat) (ha : A ≠ [])
    (t d c) (hn : (origins t).Nodup) (hr : ResidueSource t)
    (hu : UniformResidue t k) (hp : PureGroups color t) (hA : CurrentLabels A color k t)
    (o) (ho : o ∈ (run q t d c).outputs) : Keeps A o := by
  induction q generalizing t d c o with
  | zero =>
    exact step_current _ color k ha (by intros; contradiction) (by intros; contradiction)
      t d c hn hr hu hp hA o ho
  | succ q ih =>
    exact step_current (run q) color k ha
      (by intros; exact ih _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› _ ‹_›)
      (by intros; exact run_detached q _ _ _ ‹_› _ ‹_›)
      t d c hn hr hu hp hA o ho

end Universal233.KeptParent
