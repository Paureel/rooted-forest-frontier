import DegreePropagation
import PartitionRefinement

/-! Actual one-tree split at a degree-two support vertex. This module does not
supply the separate cross-tree restriction/isomorphism transport. -/
namespace DegreeTwo
open RMAF BridgeReview ExecutableBridge LeastEmbedding DegreeTwoGraph

/-- Labels with an actual leaf occurrence below the specified address. -/
def belowTest (t : Tree) (w : Vertex) (x : Nat) : Bool :=
  (terminals [x] t).any (fun p => decide (w.IsPrefix p))

def belowBlock (t : Tree) (w : Vertex) (B : List Nat) : List Nat :=
  B.filter (belowTest t w)

def outsideBlock (t : Tree) (w : Vertex) (B : List Nat) : List Nat :=
  B.filter (fun x => !belowTest t w x)

theorem belowTest_iff (t : Tree) (w : Vertex) (x : Nat) :
    belowTest t w x = true ↔ ∃ p, LeafOccurrence t p x ∧ w.IsPrefix p := by
  simp only [belowTest, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨p,hp,hw⟩
    obtain ⟨y,ho,hy⟩ := mem_terminals_iff.mp hp
    have he : y = x := by simpa using hy
    subst y
    exact ⟨p,ho,hw⟩
  · rintro ⟨p,ho,hw⟩
    exact ⟨p,mem_terminals_iff.mpr ⟨x,ho,by simp⟩,hw⟩

theorem belowBlock_mem (t : Tree) (w : Vertex) (B : List Nat) (x : Nat) :
    x ∈ belowBlock t w B ↔ x ∈ B ∧ belowTest t w x = true := by
  simp [belowBlock]

theorem outsideBlock_mem (t : Tree) (w : Vertex) (B : List Nat) (x : Nat) :
    x ∈ outsideBlock t w B ↔ x ∈ B ∧ belowTest t w x = false := by
  simp [outsideBlock]

theorem split_blocks_perm (t : Tree) (w : Vertex) (B : List Nat) :
    (belowBlock t w B ++ outsideBlock t w B).Perm B :=
  List.filter_append_perm (belowTest t w) B

theorem split_blocks_disjoint (t : Tree) (w : Vertex) (B : List Nat) :
    ∀ x, x ∈ belowBlock t w B → x ∉ outsideBlock t w B := by
  intro x hx hy
  have h1 := ((belowBlock_mem t w B x).mp hx).2
  have h2 := ((outsideBlock_mem t w B x).mp hy).2
  rw [h1] at h2
  contradiction

theorem belowBlock_support_mono (t : Tree) (w : Vertex) (B : List Nat) :
    EmbSub t (belowBlock t w B) B :=
  actual_support_mono _ _ t (fun x hx => ((belowBlock_mem t w B x).mp hx).1)

theorem outsideBlock_support_mono (t : Tree) (w : Vertex) (B : List Nat) :
    EmbSub t (outsideBlock t w B) B :=
  actual_support_mono _ _ t (fun x hx => ((outsideBlock_mem t w B x).mp hx).1)

theorem belowBlock_terminal_below (t : Tree) (w : Vertex) (B : List Nat)
    (hn : (leaves t).Nodup) :
    ∀ p, p ∈ terminals (belowBlock t w B) t → w.IsPrefix p := by
  intro p hp
  obtain ⟨x,ho,hx⟩ := mem_terminals_iff.mp hp
  obtain ⟨q,hq,hwq⟩ := (belowTest_iff t w x).mp (((belowBlock_mem t w B x).mp hx).2)
  have hpq : p = q := ho.address_unique hn hq
  simpa only [hpq] using hwq

theorem belowBlock_support_below (t : Tree) (w : Vertex) (B : List Nat)
    (hn : (leaves t).Nodup) :
    ∀ z, z ∈ minimalVertices (belowBlock t w B) t → w.IsPrefix z :=
  minimal_below_common_ancestor _ t w (belowBlock_terminal_below t w B hn)

theorem outsideBlock_support_outside (t : Tree) (w : Vertex) (B : List Nat) :
    ∀ z, z ∈ minimalVertices (outsideBlock t w B) t → ¬ w.IsPrefix z := by
  intro z hz hwz
  obtain ⟨p,hp,hzp⟩ := minimal_terminal_descendant _ t z hz
  obtain ⟨x,ho,hx⟩ := mem_terminals_iff.mp hp
  have ht := (belowTest_iff t w x).mpr ⟨p,ho,hwz.trans hzp⟩
  have hf := ((outsideBlock_mem t w B x).mp hx).2
  rw [ht] at hf
  contradiction

theorem split_supports_disjoint (t : Tree) (w : Vertex) (B : List Nat)
    (hn : (leaves t).Nodup) :
    disjointVertices (minimalVertices (belowBlock t w B) t)
      (minimalVertices (outsideBlock t w B) t) = true := by
  apply (disjointVertices_iff _ _).mpr
  intro z hz hz'
  exact outsideBlock_support_outside t w B z hz' (belowBlock_support_below t w B hn z hz)

theorem exactTwo_has_child {P : Vertex → Prop} {v : Vertex}
    (h : ExactTwo P v) : ∃ side, P (v ++ [side]) := by
  obtain ⟨a,b,hab,ha,hea,hb,heb,_⟩ := h
  rcases hea with ⟨s,hs⟩ | ⟨s,hs⟩
  · exact ⟨s,hs ▸ ha⟩
  · rcases heb with ⟨q,hq⟩ | ⟨q,hq⟩
    · exact ⟨q,hq ▸ hb⟩
    · have he : a = b := by
        have heq : a ++ [s] = b ++ [q] := hs.symm.trans hq
        exact List.append_inj_left' heq (by simp)
      exact False.elim (hab he)

theorem leaf_no_child {t : Tree} {v : Vertex} {x : Nat}
    (ho : LeafOccurrence t v x) (side : Bool) : ¬ ValidVertex t (v ++ [side]) := by
  induction ho with
  | leaf x => intro h; cases h
  | left ho ih => intro h; cases h with | left h => exact ih h
  | right ho ih => intro h; cases h with | right h => exact ih h

theorem actual_degree_two_nonterminal (B : List Nat) (t : Tree) (v : Vertex)
    (h : ExactTwo (fun z => z ∈ minimalVertices B t) v) : v ∉ terminals B t := by
  obtain ⟨side,hs⟩ := exactTwo_has_child h
  intro ht
  obtain ⟨x,ho,_⟩ := mem_terminals_iff.mp ht
  exact leaf_no_child ho side (mem_vertices_iff.mp (minimal_in_vertices B t _ hs))

theorem belowBlock_nonempty_of_child (t : Tree) (B : List Nat) (w : Vertex)
    (hw : w ∈ minimalVertices B t) : belowBlock t w B ≠ [] := by
  obtain ⟨p,hp,hwp⟩ := minimal_terminal_descendant B t w hw
  obtain ⟨x,ho,hx⟩ := mem_terminals_iff.mp hp
  have hm : x ∈ belowBlock t w B := (belowBlock_mem t w B x).mpr
    ⟨hx,(belowTest_iff t w x).mpr ⟨p,ho,hwp⟩⟩
  intro hnil
  simp [hnil] at hm

theorem child_not_prefix_parent (v : Vertex) (side : Bool) :
    ¬ (v ++ [side]).IsPrefix v := by
  intro h
  have hn := h.length_le
  simp only [List.length_append, List.length_cons, List.length_nil] at hn
  omega

theorem outsideBlock_nonempty_at_cut (t : Tree) (B : List Nat) (v : Vertex)
    (side : Bool) (hn : (leaves t).Nodup) (hv : v ∈ minimalVertices B t) :
    outsideBlock t (v ++ [side]) B ≠ [] := by
  intro hnil
  apply child_not_prefix_parent v side
  apply minimal_below_common_ancestor B t (v ++ [side]) _ v hv
  intro p hp
  obtain ⟨x,ho,hx⟩ := mem_terminals_iff.mp hp
  have ht : belowTest t (v ++ [side]) x = true := by
    cases he : belowTest t (v ++ [side]) x with
    | false =>
      have hm : x ∈ outsideBlock t (v ++ [side]) B :=
        (outsideBlock_mem t (v ++ [side]) B x).mpr ⟨hx,he⟩
      simp [hnil] at hm
    | true => rfl
  have hx0 := (belowBlock_mem t (v ++ [side]) B x).mpr ⟨hx,ht⟩
  exact belowBlock_terminal_below t (v ++ [side]) B hn p
    (mem_terminals_iff.mpr ⟨x,ho,hx0⟩)

theorem belowBlock_avoids_cut (t : Tree) (B : List Nat) (v : Vertex)
    (side : Bool) (hn : (leaves t).Nodup) :
    v ∉ minimalVertices (belowBlock t (v ++ [side]) B) t := by
  intro hv
  exact child_not_prefix_parent v side
    (belowBlock_support_below t (v ++ [side]) B hn v hv)

/-- A two-neighbor subset cannot lose any neighbor of a two-neighbor superset. -/
theorem retained_neighbor {P Q : Vertex → Prop} {v w : Vertex}
    (hsub : ∀ z, P z → Q z) (hlo : HasTwo P v) (hhi : ExactTwo Q v)
    (hw : Q w) (hew : Adj v w) : P w := by
  obtain ⟨a,b,hab,ha,hea,hb,heb⟩ := hlo
  obtain ⟨c,d,hcd,hc,hec,hd,hed,hall⟩ := hhi
  have ha' := hall a (hsub a ha) hea
  have hb' := hall b (hsub b hb) heb
  have hw' := hall w hw hew
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact False.elim (hab rfl)
  · rcases hw' with rfl | rfl <;> assumption
  · rcases hw' with rfl | rfl <;> assumption
  · exact False.elim (hab rfl)

theorem outsideBlock_avoids_cut (t : Tree) (B : List Nat) (v : Vertex)
    (side : Bool)
    (hw : v ++ [side] ∈ minimalVertices B t)
    (hdegree : ExactTwo (fun z => z ∈ minimalVertices B t) v) :
    v ∉ minimalVertices (outsideBlock t (v ++ [side]) B) t := by
  intro hv
  have hnt := actual_degree_two_nonterminal B t v hdegree
  have hnt' : v ∉ terminals (outsideBlock t (v ++ [side]) B) t := by
    intro hm
    exact hnt (terminals_mono _ B t
      (fun x hx => ((outsideBlock_mem t (v ++ [side]) B x).mp hx).1) v hm)
  have ht := actual_nonterminal_hasTwo (outsideBlock t (v ++ [side]) B) t v hv hnt'
  have hw' : v ++ [side] ∈ minimalVertices (outsideBlock t (v ++ [side]) B) t :=
    retained_neighbor (outsideBlock_support_mono t (v ++ [side]) B) ht hdegree hw
      (Or.inl ⟨side,rfl⟩)
  exact outsideBlock_support_outside t (v ++ [side]) B _ hw' (List.prefix_refl _)

theorem belowBlock_nodup (t : Tree) (w : Vertex) (B : List Nat) (hn : B.Nodup) :
    (belowBlock t w B).Nodup := hn.filter _

theorem outsideBlock_nodup (t : Tree) (w : Vertex) (B : List Nat) (hn : B.Nodup) :
    (outsideBlock t w B).Nodup := hn.filter _

/-- All one-tree local conclusions from actual exact degree two. The separate
cross-tree transport is still required for restricted agreement in u. -/
theorem actual_one_tree_split (t : Tree) (B : List Nat) (v : Vertex)
    (hn : (leaves t).Nodup) (hB : B.Nodup)
    (hv : v ∈ minimalVertices B t)
    (hdegree : ExactTwo (fun z => z ∈ minimalVertices B t) v) :
    ∃ b0 b1 : List Nat,
      b0 ≠ [] ∧ b1 ≠ [] ∧ b0.Nodup ∧ b1.Nodup ∧
      (b0 ++ b1).Perm B ∧ (∀ x, x ∈ b0 → x ∉ b1) ∧
      EmbSub t b0 B ∧ EmbSub t b1 B ∧
      disjointVertices (minimalVertices b0 t) (minimalVertices b1 t) = true ∧
      v ∉ minimalVertices b0 t ∧ v ∉ minimalVertices b1 t := by
  obtain ⟨side,hw⟩ := exactTwo_has_child hdegree
  exact ⟨belowBlock t (v ++ [side]) B, outsideBlock t (v ++ [side]) B,
    belowBlock_nonempty_of_child t B _ hw,
    outsideBlock_nonempty_at_cut t B v side hn hv,
    belowBlock_nodup t _ B hB, outsideBlock_nodup t _ B hB,
    split_blocks_perm t _ B, split_blocks_disjoint t _ B,
    belowBlock_support_mono t _ B, outsideBlock_support_mono t _ B,
    split_supports_disjoint t _ B hn,
    belowBlock_avoids_cut t B v side hn, outsideBlock_avoids_cut t B v side hw hdegree⟩

end DegreeTwo
