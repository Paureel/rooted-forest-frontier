import KeptRun

namespace Universal233.KeptParent
open RMAF CoreGraph CoreProgram Integration CutRealization Assembly SourceCoverage

abbrev keepColor (A B : List Nat) (cb : Nat → Nat) : Nat → Nat :=
  taggedColor A B (fun _ => 0) cb (fun _ => 0)

theorem initial_residue (S : Tree) (A B C : List Nat) (cb : Nat → Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (he : pairwiseEmbeddings S [A,B,C] = true) :
    ResidueSource (fromTree (keepColor A B cb) [] S) := by
  refine ⟨initialPartition S [A,B,C] (keepColor A B cb) hp he,?_⟩
  intro v c hv
  have hv' : LeafAt (recolor (keepColor A B cb) S) v c := by
    simpa only [fromTree_skeleton] using hv
  obtain ⟨x,hx,hxc⟩ := (recolor_leaf (keepColor A B cb) S v c).1 hv'
  change checkedOwner S [A,B,C] v = c % 3
  by_cases hA : x ∈ A
  · rw [checkedOwner_at_support S [A,B,C] he A (by simp) v
      ((minimalVertices_terminal A S v x hx).2 hA)]
    rw [←hxc]
    simp [keepColor,taggedColor,hA]
  · by_cases hB : x ∈ B
    · have hBA : B ≠ A := by intro h; exact hA (h ▸ hB)
      rw [checkedOwner_at_support S [A,B,C] he B (by simp) v
        ((minimalVertices_terminal B S v x hx).2 hB)]
      rw [←hxc]
      simp [keepColor,taggedColor,hA,hB,List.idxOf_cons,Ne.symm hBA,hBA]
    · obtain ⟨b,hb,hxb⟩ := partitionCheck_covers (leaves S) [A,B,C] hp x (leafAt_label S v x hx)
      have hC : x ∈ C := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
        rcases hb with rfl | rfl | rfl
        · exact False.elim (hA hxb)
        · exact False.elim (hB hxb)
        · exact hxb
      have hCA : C ≠ A := by intro h; exact hA (h ▸ hC)
      have hCB : C ≠ B := by intro h; exact hB (h ▸ hC)
      rw [checkedOwner_at_support S [A,B,C] he C (by simp) v
        ((minimalVertices_terminal C S v x hx).2 hC)]
      rw [←hxc]
      simp [keepColor,taggedColor,hA,hB,List.idxOf_cons,Ne.symm hCA,Ne.symm hCB,hCA,hCB]

theorem initial_uniform (S : Tree) (A B : List Nat) (cb : Nat → Nat) (k : Nat)
    (hk : k = 0 ∨ k = 2) : UniformResidue (fromTree (keepColor A B cb) [] S) k := by
  intro v c hv hc
  have hv' : LeafAt (recolor (keepColor A B cb) S) v c := by
    simpa only [fromTree_skeleton] using hv
  obtain ⟨x,hx,hxc⟩ := (recolor_leaf (keepColor A B cb) S v c).1 hv'
  rw [←hxc] at hc ⊢
  rcases hk with rfl | rfl <;>
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;>
    simp [keepColor,taggedColor,ha,hb] at hc ⊢ <;> omega

theorem generate_keeps_special (S : Tree) (A B C L : List Nat) (cb : Nat → Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (he : pairwiseEmbeddings S [A,B,C] = true) (k : Nat) (hk : k = 0 ∨ k = 2)
    (hne : L ≠ [])
    (hL : ∀ x, x ∈ L ↔ x ∈ leaves S ∧ keepColor A B cb x = k)
    (q : Nat) (o : Output) (ho : o ∈ (generate S (keepColor A B cb) q).outputs) : Keeps L o := by
  unfold generate at ho
  split at ho
  · apply run_keeps_current _ (keepColor A B cb) k hne _ [] []
      (fromTree_origins_nodup _ _ _) (initial_residue S A B C cb hp he)
      (initial_uniform S A B cb k hk) (fromTree_pure _ _ _) _ o ho
    intro x
    simpa only [fromTree_payload] using hL x
  · simp at ho

theorem checked_parent_disjoint (S : Tree) (A B C : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true) :
    (∀ x, x ∈ A → x ∈ B → False) ∧ (∀ x, x ∈ A → x ∈ C → False) ∧
    (∀ x, x ∈ B → x ∈ C → False) := by
  have hn : ([A,B,C].flatten).Nodup := by
    have hc : (leaves S).all (fun x => [A,B,C].flatten.count x == 1) = true := by
      simp only [partitionCheck,Bool.and_eq_true] at hp
      exact hp.1.2
    apply List.nodup_iff_count_of_mem.2
    intro x hx
    exact beq_iff_eq.1 (List.all_eq_true.1 hc x (partitionCheck_subset _ _ hp hx))
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil] at hn
  obtain ⟨hA,hBC,hdA⟩ := List.nodup_append.1 hn
  obtain ⟨hB,hC,hdB⟩ := List.nodup_append.1 hBC
  exact ⟨fun x hx hy => hdA x hx x (List.mem_append_left C hy) rfl,
    fun x hx hy => hdA x hx x (List.mem_append_right B hy) rfl,
    fun x hx hy => hdB x hx x hy rfl⟩

/-- The public universal forall-output theorem, with actual ORIGINAL source
partition and embedding checks. B's local coloring is completely arbitrary. -/
theorem generated_keeps_A_C (S : Tree) (A B C : List Nat) (cb : Nat → Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (he : pairwiseEmbeddings S [A,B,C] = true)
    (q : Nat) (o : Output) (ho : o ∈ (generate S (keepColor A B cb) q).outputs) :
    Keeps A o ∧ Keeps C o := by
  have hsub := partitionCheck_subset (leaves S) [A,B,C] hp
  have hdis := checked_parent_disjoint S A B C hp
  constructor
  · apply generate_keeps_special S A B C A cb hp he 0 (Or.inl rfl)
      (partitionCheck_nonempty (leaves S) [A,B,C] hp A (by simp)) _ q o ho
    intro x
    constructor
    · intro hx
      exact ⟨hsub (List.mem_flatten.2 ⟨A,by simp,hx⟩),by simp [keepColor,taggedColor,hx]⟩
    · rintro ⟨hx,hcol⟩
      by_cases ha : x ∈ A
      · exact ha
      · unfold keepColor taggedColor at hcol
        simp only [ha,ite_false] at hcol
        split at hcol <;> omega
  · apply generate_keeps_special S A B C C cb hp he 2 (Or.inr rfl)
      (partitionCheck_nonempty (leaves S) [A,B,C] hp C (by simp)) _ q o ho
    intro x
    constructor
    · intro hx
      have ha : x ∉ A := fun ha => hdis.2.1 x ha hx
      have hb : x ∉ B := fun hb => hdis.2.2 x hb hx
      exact ⟨hsub (List.mem_flatten.2 ⟨C,by simp,hx⟩),by simp [keepColor,taggedColor,ha,hb]⟩
    · rintro ⟨hx,hcol⟩
      have ha : x ∉ A := by intro ha; simp [keepColor,taggedColor,ha] at hcol
      have hb : x ∉ B := by
        intro hb
        simp [keepColor,taggedColor,ha,hb] at hcol
        omega
      obtain ⟨b,hb',hxb⟩ := partitionCheck_covers (leaves S) [A,B,C] hp x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hb'
      rcases hb' with rfl | rfl | rfl
      · exact False.elim (ha hxb)
      · exact False.elim (hb hxb)
      · exact hxb

end Universal233.KeptParent
