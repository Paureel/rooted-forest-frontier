import Parents
namespace BinaryExchange
open RMAF VertexGeometry

theorem inside_refl (A : List Nat) : inside A A = true :=
  (inside_iff A A).2 (fun _ hx => hx)

theorem outside_filter (A B : List Nat) (F : List (List Nat)) :
    outside A B F = F.filter (fun C => !inside C B && !inside C A) := by
  simp only [outside,residual,List.filter_filter]

theorem filter_nil {α : Type} (L : List α) (p : α → Bool)
    (h : ∀ x, x ∈ L → p x = false) : L.filter p = [] := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp [h x (by simp),ih (by intro y hy; exact h y (by simp [hy]))]

theorem output_outside (A B : List Nat) (V W : List (List Nat)) (q : Nat → Bool)
    (hV : ∀ C, C ∈ V → Sub C B)
    (hW : ∀ C, C ∈ W → inside C A = false ∧ inside C B = false) :
    outside A B (output A V W q) = W := by
  rw [outside_filter]
  have hs : (splitAll V q).filter (fun C => !inside C B && !inside C A) = [] := by
    apply filter_nil
    intro C hC
    obtain ⟨E,hE,hCE⟩ := List.mem_flatMap.1 hC
    have hi : inside C B = true := (inside_iff C B).2 (by intro x hx; exact hV E hE x (split_sub E C q hCE x hx))
    simp [hi]
  have hw : W.filter (fun C => !inside C B && !inside C A) = W := by
    apply List.filter_eq_self.2
    intro C hC
    simp [(hW C hC).1,(hW C hC).2]
  simp [output,inside_refl,List.filter_append,hs,hw]

theorem output_refines (A B : List Nat) (P F V W : List (List Nat)) (q : Nat → Bool)
    (hA : A ∈ P) (hB : B ∈ P) (hf : Refines F P)
    (hV : ∀ C, C ∈ V → Sub C B) (hW : ∀ C, C ∈ W → C ∈ F) :
    Refines (output A V W q) P := by
  intro C hC
  rcases List.mem_cons.1 hC with hC | hC
  · subst C; exact ⟨A,hA,fun _ hx => hx⟩
  · rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨E,hE,hCE⟩ := List.mem_flatMap.1 hC
      exact ⟨B,hB,by intro x hx; exact hV E hE x (split_sub E C q hCE x hx)⟩
    · exact hf C (hW C hC)

theorem output_B_mono (A B : List Nat) (V W : List (List Nat)) (q : Nat → Bool)
    (hneA : A ≠ []) (hd : ∀ x, x ∈ A → x ∉ B)
    (hW : ∀ C, C ∈ W → inside C B = false) :
    ∀ C, C ∈ output A V W q → Sub C B →
      (∀ x, x ∈ C → q x = true) ∨ (∀ x, x ∈ C → q x = false) := by
  intro C hC hCB
  rcases List.mem_cons.1 hC with hC | hC
  · subst C
    obtain ⟨x,hx⟩ := nonempty_witness A hneA
    exact False.elim (hd x hx (hCB x hx))
  · rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨E,hE,hCE⟩ := List.mem_flatMap.1 hC
      exact split_mono E q C hCE
    · have hh := (inside_iff C B).2 hCB
      simp [hW C hC] at hh

theorem output_A_once (A B : List Nat) (V W : List (List Nat)) (q : Nat → Bool)
    (hneA : A ≠ []) (hd : ∀ x, x ∈ A → x ∉ B)
    (hV : ∀ C, C ∈ V → Sub C B)
    (hW : ∀ C, C ∈ W → inside C A = false) :
    (output A V W q).count A = 1 := by
  have hs : A ∉ splitAll V q := by
    intro ha
    obtain ⟨C,hC,hAC⟩ := List.mem_flatMap.1 ha
    obtain ⟨x,hx⟩ := nonempty_witness A hneA
    exact hd x hx (hV C hC x (split_sub C A q hAC x hx))
  have hw : A ∉ W := by
    intro ha
    have hh := hW A ha
    simp [inside_refl] at hh
  simp [output,List.count_cons,List.count_append,List.count_eq_zero.2 hs,List.count_eq_zero.2 hw]

/-- Executable binary E exchange. All trees/partitions and all collision tests
are the original RMAF objects. Source cut-cost reconstruction is not asserted. -/
def exchange (A B : List Nat) (F : List (List Nat)) (u : Tree) :=
  output A (bParts A B F) (outside A B F) ((leaves u).contains ·)

/-- Universal E, with every original graph hypothesis exposed. The bilateral
mutual-clear assumption is retained even though the surgery uses its B-sector
half. No whole-parent-B topology agreement is required. -/
theorem binary_exchange (s t u : Tree) (P : List (List Nat)) (A B : List Nat)
    (v : RMAF.Vertex)
    (_hs : (leaves s).Nodup) (ht : (leaves t).Nodup)
    (_sameLabels : ∀ x, x ∈ leaves s ↔ x ∈ leaves t)
    (hP : partitionCheck (leaves s) P = true)
    (hPS : pairwiseEmbeddings s P = true)
    (hAparent : A ∈ P) (hBparent : B ∈ P) (hAB : A ≠ B)
    (_edge : v ≠ []) (hedge : treeAt t v = some u)
    (hAm : mixed A ((leaves u).contains ·) = true)
    (_hBm : mixed B ((leaves u).contains ·) = true)
    (_clearAY : Disj t (yes A ((leaves u).contains ·)) B)
    (_clearAN : Disj t (no A ((leaves u).contains ·)) B)
    (clearBY : Disj t (yes B ((leaves u).contains ·)) A)
    (clearBN : Disj t (no B ((leaves u).contains ·)) A)
    (clearOther : ∀ E, E ∈ P → E ≠ A → E ≠ B → Disj t E A ∧ Disj t E B)
    (hA : restrictionAgrees s t A = true)
    (F : List (List Nat)) (hF : agreement s t F = true) (hf : Refines F P) :
    let F' := exchange A B F u
    agreement s t F' = true ∧ Refines F' P ∧ F'.count A = 1 ∧
      (∀ C, C ∈ F' → Sub C B →
        (∀ x, x ∈ C → x ∈ leaves u) ∨ (∀ x, x ∈ C → x ∉ leaves u)) ∧
      F'.length ≤ F.length ∧ outside A B F' = outside A B F := by
  let U := aParts A F
  let V := bParts A B F
  let W := outside A B F
  let q : Nat → Bool := fun x => (leaves u).contains x
  have hperm : (U ++ V ++ W).Perm F := grouped_perm A B F
  have hFg := agreement_perm s t F (U ++ V ++ W) hperm.symm hF
  have hparts := agreement_parts s t F hF
  have hU := apart_partition (leaves s) P F hP hparts.1 hf A hAparent
  have hnA := parent_nodup (leaves s) P hP A hAparent
  have hneA := (partition_parts (leaves s) P hP).1 A hAparent
  have hVB : ∀ C, C ∈ V → Sub C B := bparts_sub A B F
  have hWorig : ∀ C, C ∈ W → C ∈ F ∧ inside C A = false ∧ inside C B = false := outside_original A B F
  have hpS := (executable_pairwiseEmbeddings s P).1 hPS
  have hSAB : Disj s A B := pairwise_mem (fun _ _ h => disj_symm h) P hpS A B hAparent hBparent hAB
  have hSAW : ∀ C, C ∈ W → Disj s A C := by
    intro C hC
    obtain ⟨E,hE,hEA,hEB,hCE⟩ := outside_parent (leaves s) P F hf A B C hC
    exact disj_mono (pairwise_mem (fun _ _ h => disj_symm h) P hpS A E hAparent hE (Ne.symm hEA))
      (fun _ hx => hx) hCE
  have hTAW : ∀ C, C ∈ W → Disj t A C := by
    intro C hC
    obtain ⟨E,hE,hEA,hEB,hCE⟩ := outside_parent (leaves s) P F hf A B C hC
    exact disj_mono (disj_symm (clearOther E hE hEA hEB).1) (fun _ hx => hx) hCE
  have hvalid := exchange_valid s t u v A B U V W ht hedge hnA hneA hU hVB hFg hA hSAB hSAW
    (disj_symm clearBY) (disj_symm clearBN) hTAW
  have hlen := exchange_size s t u v A U V W ht hedge hU hFg hAm
  have hdisj := parent_disjoint (leaves s) P hP A B hAparent hBparent hAB
  refine ⟨hvalid,output_refines A B P F V W q hAparent hBparent hf hVB (fun C hC => (hWorig C hC).1),
    output_A_once A B V W q hneA hdisj hVB (fun C hC => (hWorig C hC).2.1),?_,?_,?_⟩
  · intro C hC hCB
    rcases output_B_mono A B V W q hneA hdisj (fun C hC => (hWorig C hC).2.2) C hC hCB with hy | hn
    · exact Or.inl (by intro x hx; exact List.contains_iff_mem.1 (hy x hx))
    · exact Or.inr (by
        intro x hx
        have hqx : (leaves u).contains x = false := hn x hx
        simpa using hqx)
  · exact Nat.le_trans hlen (Nat.le_of_eq hperm.length_eq)
  · exact output_outside A B V W q hVB (fun C hC => (hWorig C hC).2)
end BinaryExchange
