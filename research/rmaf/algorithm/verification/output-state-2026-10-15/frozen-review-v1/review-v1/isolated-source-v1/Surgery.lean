import Forest
namespace BinaryExchange
open RMAF VertexGeometry

def output (A : List Nat) (V W : List (List Nat)) (q : Nat → Bool) :=
  A :: (splitAll V q ++ W)

theorem exchange_counts (A : List Nat) (U V W : List (List Nat)) (q : Nat → Bool)
    (hnA : A.Nodup) (hU : partitionCheck A U = true) (x) :
    (output A V W q).flatten.count x = (U ++ V ++ W).flatten.count x := by
  have hu := partition_count A U hU x
  have ha := hnA.count (a := x)
  simp only [output,List.flatten_cons,List.flatten_append,List.count_append,splitAll_count]
  omega

theorem exchange_partition (L A : List Nat) (U V W : List (List Nat)) (q : Nat → Bool)
    (hnA : A.Nodup) (hneA : A ≠ []) (hU : partitionCheck A U = true)
    (hp : partitionCheck L (U ++ V ++ W) = true) :
    partitionCheck L (output A V W q) = true := by
  obtain ⟨hn,hc,hl⟩ := partition_parts L _ hp
  apply partition_intro
  · intro C hC
    rcases List.mem_cons.1 hC with hC | hC
    · simpa [hC] using hneA
    · rcases List.mem_append.1 hC with hC | hC
      · exact splitAll_nonempty V q C hC
      · exact hn C (by simp [hC])
  · intro x hx
    rw [exchange_counts A U V W q hnA hU]
    exact hc x hx
  · intro x hx
    apply hl x
    apply List.count_pos_iff.1
    rw [← exchange_counts A U V W q hnA hU]
    exact List.count_pos_iff.2 hx

/-- Full actual-AF surgery for a displayed family U of A blocks, V of B blocks,
and untouched W. The final theorem must derive this decomposition from P. -/
theorem exchange_valid (s t u : Tree) (v : RMAF.Vertex) (A B : List Nat)
    (U V W : List (List Nat))
    (ht : (leaves t).Nodup) (hedge : treeAt t v = some u)
    (hnA : A.Nodup) (hneA : A ≠ []) (hU : partitionCheck A U = true)
    (hVB : ∀ C, C ∈ V → Sub C B)
    (hF : agreement s t (U ++ V ++ W) = true)
    (hA : restrictionAgrees s t A = true)
    (hSAB : Disj s A B) (hSAW : ∀ C, C ∈ W → Disj s A C)
    (hTY : Disj t A (yes B ((leaves u).contains ·)))
    (hTN : Disj t A (no B ((leaves u).contains ·)))
    (hTAW : ∀ C, C ∈ W → Disj t A C) :
    agreement s t (output A V W ((leaves u).contains ·)) = true := by
  let q : Nat → Bool := fun x => (leaves u).contains x
  obtain ⟨hps,hpt,hshape,hpairs,hpairt⟩ := agreement_parts s t _ hF
  obtain ⟨hUVs,hWs,hUVW_s⟩ := List.pairwise_append.1 hpairs
  obtain ⟨hUs,hVs,hUV_s⟩ := List.pairwise_append.1 hUVs
  obtain ⟨hUVt,hWt,hUVW_t⟩ := List.pairwise_append.1 hpairt
  obtain ⟨hUt,hVt,hUV_t⟩ := List.pairwise_append.1 hUVt
  have hsplits : ∀ C, C ∈ V → Disj s (yes C q) (no C q) := by
    intro C hC
    have hh := descendant_agreed_split s t u v C ht hedge (hshape C (by simp [hC]))
    exact (executable_disjointVertices s _ _).1 hh.2.1
  have hsplitT : ∀ C, C ∈ V → Disj t (yes C q) (no C q) := by
    intro C hC
    have hh := descendant_agreed_split s t u v C ht hedge (hshape C (by simp [hC]))
    exact (executable_disjointVertices t _ _).1 hh.2.2
  have hnewpairs : (output A V W q).Pairwise (Disj s) := by
    apply List.pairwise_cons.2
    refine ⟨?_,List.pairwise_append.2 ⟨splitAll_pairwise s V q hVs hsplits,hWs,?_⟩⟩
    · intro C hC
      rcases List.mem_append.1 hC with hC | hC
      · obtain ⟨E,hE,hCE⟩ := List.mem_flatMap.1 hC
        exact disj_mono hSAB (fun _ hx => hx) (fun x hx => hVB E hE x (split_sub E C q hCE x hx))
      · exact hSAW C hC
    · intro C hC E hE
      obtain ⟨D,hD,hCD⟩ := List.mem_flatMap.1 hC
      exact disj_mono (hUVW_s D (by simp [hD]) E hE) (split_sub D C q hCD) (fun _ hx => hx)
  have hnewpairt : (output A V W q).Pairwise (Disj t) := by
    apply List.pairwise_cons.2
    refine ⟨?_,List.pairwise_append.2 ⟨splitAll_pairwise t V q hVt hsplitT,hWt,?_⟩⟩
    · intro C hC
      rcases List.mem_append.1 hC with hC | hC
      · obtain ⟨E,hE,hCE⟩ := List.mem_flatMap.1 hC
        rcases (mem_split E C q).1 hCE with ⟨hcol,hne⟩
        rcases hcol with rfl | rfl
        · exact disj_mono hTY (fun _ hx => hx) (by intro x hx; obtain ⟨hxe,hq⟩ := List.mem_filter.1 hx; exact List.mem_filter.2 ⟨hVB E hE x hxe,hq⟩)
        · exact disj_mono hTN (fun _ hx => hx) (by intro x hx; obtain ⟨hxe,hq⟩ := List.mem_filter.1 hx; exact List.mem_filter.2 ⟨hVB E hE x hxe,hq⟩)
      · exact hTAW C hC
    · intro C hC E hE
      obtain ⟨D,hD,hCD⟩ := List.mem_flatMap.1 hC
      exact disj_mono (hUVW_t D (by simp [hD]) E hE) (split_sub D C q hCD) (fun _ hx => hx)
  have hnewshape : ∀ C, C ∈ output A V W q → restrictionAgrees s t C = true := by
    intro C hC
    rcases List.mem_cons.1 hC with hC | hC
    · subst C; exact hA
    · rcases List.mem_append.1 hC with hC | hC
      · obtain ⟨E,hE,hCE⟩ := List.mem_flatMap.1 hC
        have hne := ((mem_split E C q).1 hCE).2
        have hex : ∃ x, x ∈ C := by cases C with
          | nil => contradiction
          | cons x xs => exact ⟨x,by simp⟩
        obtain ⟨x,hx⟩ := hex
        have hEl := partition_sub (leaves s) _ hps E (by simp [hE])
        exact restrictionAgrees_sub s t E C (hshape E (by simp [hE])) (split_sub E C q hCE)
          ⟨x,hx,hEl x (split_sub E C q hCE x hx)⟩
      · exact hshape C (by simp [hC])
  unfold agreement
  simp only [Bool.and_eq_true,List.all_eq_true,executable_pairwiseEmbeddings]
  exact ⟨⟨⟨⟨exchange_partition (leaves s) A U V W q hnA hneA hU hps,
    exchange_partition (leaves t) A U V W q hnA hneA hU hpt⟩,hnewshape⟩,hnewpairs⟩,hnewpairt⟩

def mixed (C : List Nat) (q : Nat → Bool) : Bool :=
  !(yes C q).isEmpty && !(no C q).isEmpty

theorem nonempty_witness {α : Type} (L : List α) (h : L ≠ []) : ∃ x, x ∈ L := by
  cases L with
  | nil => contradiction
  | cons x xs => exact ⟨x,by simp⟩

theorem mixed_iff (C : List Nat) (q : Nat → Bool) :
    mixed C q = true ↔ (∃ x, x ∈ C ∧ q x = true) ∧ (∃ y, y ∈ C ∧ q y = false) := by
  simp only [mixed,Bool.and_eq_true,Bool.not_eq_true',isEmpty_false]
  constructor
  · rintro ⟨hy,hn⟩
    obtain ⟨x,hx⟩ := nonempty_witness _ hy
    obtain ⟨y,hy⟩ := nonempty_witness _ hn
    exact ⟨⟨x,(List.mem_filter.1 hx).1,(List.mem_filter.1 hx).2⟩,
      ⟨y,(List.mem_filter.1 hy).1,by simpa using (List.mem_filter.1 hy).2⟩⟩
  · rintro ⟨⟨x,hx,hqx⟩,⟨y,hy,hqy⟩⟩
    exact ⟨by intro he; have hm : x ∈ yes C q := List.mem_filter.2 ⟨hx,hqx⟩; simpa [he] using hm,
      by intro he; have hm : y ∈ no C q := List.mem_filter.2 ⟨hy,by simpa using hqy⟩; simpa [he] using hm⟩

theorem split_length (C : List Nat) (q : Nat → Bool) :
    (split C q).length ≤ 1 + (if mixed C q then 1 else 0) := by
  cases hy : (yes C q).isEmpty <;> cases hn : (no C q).isEmpty <;>
    simp [split,mixed,hy,hn]

theorem splitAll_length (V : List (List Nat)) (q : Nat → Bool) :
    (splitAll V q).length ≤ V.length + (V.filter (mixed · q)).length := by
  induction V with
  | nil => simp [splitAll]
  | cons C V ih =>
    have hc := split_length C q
    cases hm : mixed C q <;> simp [splitAll,List.filter_cons,hm] at ih ⊢ <;> simp [hm] at hc <;> omega

theorem marked_at_most_one (V : List (List Nat)) (m : List Nat → Bool)
    (R : List Nat → List Nat → Prop) (hp : V.Pairwise R)
    (h : ∀ C, C ∈ V → ∀ E, E ∈ V → R C E → m C = true → m E = true → False) :
    (V.filter m).length ≤ 1 := by
  induction V with
  | nil => simp
  | cons C V ih =>
    obtain ⟨hc,hv⟩ := List.pairwise_cons.1 hp
    have ihv := ih hv (by intro D hD E hE; exact h D (by simp [hD]) E (by simp [hE]))
    cases hm : m C
    · simpa [hm] using ihv
    · have he : V.filter m = [] := by
        cases hvf : V.filter m with
        | nil => rfl
        | cons E Es =>
          have hE : E ∈ V.filter m := by simp [hvf]
          obtain ⟨hEV,hmE⟩ := List.mem_filter.1 hE
          exact False.elim (h C (by simp) E (by simp [hEV]) (hc E hEV) hm hmE)
      simp [hm,he]
end BinaryExchange
