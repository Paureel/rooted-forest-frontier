import Lemmas

namespace Universal233.DepthOne
open RMAF CoreGraph CutRealization RestrictionBridge Integration

def twoColor (A : List Nat) (x : Nat) : Nat := if x ∈ A then 0 else 1

theorem checked_pair_union (L A B : List Nat) (hp : partitionCheck L [A,B] = true)
    {x : Nat} (hx : x ∈ L) : x ∈ A ∨ x ∈ B := by
  obtain ⟨U,hU,hxU⟩ := checked_covers L [A,B] hp hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hU
  rcases hU with rfl | rfl
  · exact Or.inl hxU
  · exact Or.inr hxU

theorem checked_shared_block (L : List Nat) (Q : List (List Nat))
    (hp : partitionCheck L Q = true) (U V : List Nat) (hU : U ∈ Q) (hV : V ∈ Q)
    (x : Nat) (hxU : x ∈ U) (hxV : x ∈ V) : U = V := by
  obtain ⟨W,hW,hxW,hc,unique⟩ := unique_label_owner Q x
    (checked_count L Q hp (checked_label L Q hp hU hxU))
  exact (unique U hU hxU).trans (unique V hV hxV).symm

theorem twoColor_mono (L A B : List Nat) (hp : partitionCheck L [A,B] = true) :
    ∀ U, U ∈ [A,B] → VertexGeometry.LabelMonochromatic (twoColor A) U := by
  intro U hU x y hx hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hU
  rcases hU with hU | hU
  · subst U; simp [twoColor,hx,hy]
  · subst U
    have hnx : x ∉ A := fun h => checked_disjoint L A B hp x h hx
    have hny : y ∉ A := fun h => checked_disjoint L A B hp y h hy
    simp [twoColor,hnx,hny]

theorem output_class (L A B : List Nat) (Q : List (List Nat))
    (hp : partitionCheck L [A,B] = true) (hq : partitionCheck L Q = true)
    (href : VertexGeometry.Refines [A,B] Q)
    (hm : ∀ U, U ∈ Q → VertexGeometry.LabelMonochromatic (twoColor A) U)
    (U : List Nat) (hU : U ∈ Q) :
    (∀ x, x ∈ U ↔ x ∈ A) ∨ (∀ x, x ∈ U ↔ x ∈ B) := by
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil U (checked_nonempty L Q hq U hU)
  by_cases hxa : x ∈ A
  · obtain ⟨V,hV,hAV⟩ := href A (by simp)
    have hVU := checked_shared_block L Q hq V U hV hU x (hAV x hxa) hx
    subst V
    left
    intro y
    constructor
    · intro hy
      have hcol := hm U hU x y hx hy
      simpa [twoColor,hxa] using hcol.symm
    · exact hAV y
  · have hxb : x ∈ B := (checked_pair_union L A B hp (checked_label L Q hq hU hx)).resolve_left hxa
    obtain ⟨V,hV,hBV⟩ := href B (by simp)
    have hVU := checked_shared_block L Q hq V U hV hU x (hBV x hxb) hx
    subst V
    right
    intro y
    constructor
    · intro hy
      have hcol := hm U hU x y hx hy
      have hnya : y ∉ A := by
        intro hya
        simp [twoColor,hxa,hya] at hcol
      exact (checked_pair_union L A B hp (checked_label L Q hq hU hy)).resolve_left hnya
    · exact hBV y

theorem two_distinct_length {α : Type} (Q : List α) (U V : α)
    (hU : U ∈ Q) (hV : V ∈ Q) (hne : U ≠ V) : 2 ≤ Q.length := by
  cases Q with
  | nil => simp at hU
  | cons C Q =>
    cases Q with
    | nil => have hu : U = C := by simpa using hU
             have hv : V = C := by simpa using hV
             exact False.elim (hne (hu.trans hv.symm))
    | cons D Q => simp

theorem two_output_blocks (L A B : List Nat) (Q : List (List Nat))
    (hp : partitionCheck L [A,B] = true)
    (href : VertexGeometry.Refines [A,B] Q)
    (hm : ∀ U, U ∈ Q → VertexGeometry.LabelMonochromatic (twoColor A) U) :
    2 ≤ Q.length := by
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil A (checked_nonempty L [A,B] hp A (by simp))
  obtain ⟨y,hy⟩ := List.exists_mem_of_ne_nil B (checked_nonempty L [A,B] hp B (by simp))
  obtain ⟨U,hU,hAU⟩ := href A (by simp)
  obtain ⟨V,hV,hBV⟩ := href B (by simp)
  apply two_distinct_length Q U V hU hV
  intro he
  subst V
  have hny : y ∉ A := fun h => checked_disjoint L A B hp y h hy
  have hc := hm U hU x y (hAU x hx) (hBV y hy)
  simp [twoColor,hx,hny] at hc

theorem component_subtree_members (S : Tree) (p : Vertex) (L : List Nat)
    (h : ComponentLabels S [p] p L) : ∀ x, x ∈ L ↔ x ∈ subtreeLabels S p := by
  intro x
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := h.labelsValid x hx
    have hw := (h.exact a x ha).1 hx
    have hr := (region_component (Or.inr (by simp)) h.actual (region_self [p] p)).1 hw
    exact (subtreeLabels_mem S p x).2 ⟨a,ha,hr.2.1⟩
  · intro hx
    obtain ⟨a,ha,hpa⟩ := (subtreeLabels_mem S p x).1 hx
    apply (h.exact a x ha).2
    apply (region_component (Or.inr (by simp)) h.actual (region_self [p] p)).2
    refine ⟨ha.valid,hpa,?_⟩
    intro q hq hqa
    have he : q = p := by simpa using hq
    subst q
    exact List.prefix_rfl

/-- The only production-core use is proof-only source reconstruction. The
executable pretest above enumerates original edges directly. -/
theorem source_two_split (S : Tree) (A B : List Nat)
    (hn : (leaves S).Nodup) (hp : partitionCheck (leaves S) [A,B] = true)
    (he : pairwiseEmbeddings S [A,B] = true) :
    ∃ p, p ∈ edges S ∧ ((subtreeLabels S p).Perm A ∨ (subtreeLabels S p).Perm B) := by
  obtain ⟨o,ho,hq,href,hreal,hmono,hlo,hhi⟩ := checked_source_core S [A,B] (twoColor A)
    hn hp he (twoColor_mono (leaves S) A B hp)
  have htwo := two_output_blocks (leaves S) A B o.partition hp href hmono
  obtain ⟨good,actual,comps,hroots,hblocks,hlabels,hnd,hcover,hsep,hno,hcost⟩ := hreal
  have hlen : o.sourceCuts.length = 1 := by simp only [List.length_cons,List.length_nil] at hhi; omega
  obtain ⟨p,hcuts⟩ : ∃ p, o.sourceCuts = [p] := by
    cases hc : o.sourceCuts with
    | nil => simp [hc] at hlen
    | cons p ps =>
      have hz : ps = [] := List.length_eq_zero_iff.1 (by simpa [hc] using hlen)
      exact ⟨p,by simp [hc,hz]⟩
  have hact : Valid S p := actual p (by simp [hcuts])
  have hnr : p ≠ [] := good.2 p (by simp [hcuts])
  have hpm : p ∈ comps.map Prod.fst := by rw [hroots,hcuts]; simp
  obtain ⟨pair,hpair,hepair⟩ := List.mem_map.1 hpm
  have hpairEq : pair = (p,pair.2) := by cases pair; simp_all
  have hcomponent : ComponentLabels S [p] p pair.2 := by
    rw [←hcuts]
    exact hlabels p pair.2 (hpairEq ▸ hpair)
  have hclass : pair.2 ∈ o.partition := by rw [←hblocks]; exact List.mem_map.2 ⟨pair,hpair,rfl⟩
  have hmatch := component_subtree_members S p pair.2 hcomponent
  have hA := checked_block_nodup (leaves S) [A,B] hn hp A (by simp)
  have hB := checked_block_nodup (leaves S) [A,B] hn hp B (by simp)
  refine ⟨p,(mem_edges S p).2 ⟨hact,hnr⟩,?_⟩
  rcases output_class (leaves S) A B o.partition hp hq href hmono pair.2 hclass with h | h
  · left
    apply (List.perm_ext_iff_of_nodup (subtreeLabels_nodup S p hn) hA).2
    intro x
    exact (hmatch x).symm.trans (h x)
  · right
    apply (List.perm_ext_iff_of_nodup (subtreeLabels_nodup S p hn) hB).2
    intro x
    exact (hmatch x).symm.trans (h x)

theorem complement_perm (S : Tree) (A B : List Nat) (p : Vertex)
    (hn : (leaves S).Nodup) (hp : partitionCheck (leaves S) [A,B] = true)
    (hA : (subtreeLabels S p).Perm A) : (complement S p).Perm B := by
  apply (List.perm_ext_iff_of_nodup (hn.filter _) (checked_block_nodup _ _ hn hp B (by simp))).2
  intro x
  simp only [complement,List.mem_filter,Bool.not_eq_true',Bool.eq_false_iff,List.contains_iff_mem]
  constructor
  · rintro ⟨hxs,hxn⟩
    exact (checked_pair_union (leaves S) A B hp hxs).resolve_left
      (fun h => hxn (List.contains_iff_mem.2 (hA.mem_iff.2 h)))
  · intro hxb
    exact ⟨checked_label (leaves S) [A,B] hp (by simp) hxb,
      fun h => checked_disjoint (leaves S) A B hp x (hA.mem_iff.1 (List.contains_iff_mem.1 h)) hxb⟩

theorem two_block_complete (T S : Tree) (A B : List Nat)
    (hn : (leaves S).Nodup) (ha : agreement T S [A,B] = true) :
    ∃ p, p ∈ edges S ∧ agreement T S (forest S (some p)) = true := by
  have hh := ha
  simp only [agreement,Bool.and_eq_true] at hh
  have hp := hh.1.1.1.2
  obtain ⟨p,hpedge,hAB⟩ := source_two_split S A B hn hp hh.2
  refine ⟨p,hpedge,?_⟩
  rcases hAB with hA | hB
  · have hB := complement_perm S A B p hn hp hA
    rw [forest,←agreement_pair_perm T S A B _ _ hA.symm hB.symm]
    exact ha
  · have has : agreement T S [B,A] = true := by rw [←agreement_pair_swap T S A B]; exact ha
    have hhs := has
    simp only [agreement,Bool.and_eq_true] at hhs
    have hA := complement_perm S B A p hn hhs.1.1.1.2 hB
    rw [forest,←agreement_pair_perm T S B A _ _ hB.symm hA.symm]
    exact has

end Universal233.DepthOne
