import RecoveryProgram

namespace Universal233.FinalCutRecovery
open RMAF CoreProgram SourceCoverage VertexGeometry RankDichotomy

theorem head_mem (b : List Nat) (h : b ≠ []) : b.headD 0 ∈ b := by
  cases b <;> simp_all

theorem checked_flatten_nodup (S : Tree) (P : List (List Nat))
    (hp : partitionCheck (leaves S) P = true) : P.flatten.Nodup := by
  apply List.nodup_iff_count_of_mem.2
  intro x hx
  have hs := partitionCheck_subset _ P hp hx
  have hh : (leaves S).all (fun x => P.flatten.count x == 1) = true := by
    simp only [partitionCheck,Bool.and_eq_true] at hp
    exact hp.1.2
  exact beq_iff_eq.1 (List.all_eq_true.1 hh x hs)

theorem color_of_mem (P : List (List Nat)) (hn : P.flatten.Nodup)
    (b : List Nat) (hb : b ∈ P) (x : Nat) (hx : x ∈ b) :
    blockColor P x = b.headD 0 := by
  induction P with
  | nil => simp at hb
  | cons a P ih =>
    have hh := List.nodup_append.1 (show (a ++ P.flatten).Nodup from hn)
    rcases List.mem_cons.1 hb with he | hb
    · subst b; simp [blockColor,hx]
    · have hxP : x ∈ P.flatten := List.mem_flatten.2 ⟨b,hb,hx⟩
      have hxa : x ∉ a := fun ha => hh.2.2 x ha x hxP rfl
      simpa [blockColor,hxa] using ih hh.2.1 hb

theorem representative_nodup (P : List (List Nat)) (hn : P.flatten.Nodup)
    (he : ∀ b, b ∈ P → b ≠ []) : (P.map (fun b => b.headD 0)).Nodup := by
  induction P with
  | nil => simp
  | cons a P ih =>
    have hh := List.nodup_append.1 (show (a ++ P.flatten).Nodup from hn)
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih hh.2.1 (fun b hb => he b (by simp [hb]))⟩
    intro hm
    obtain ⟨b,hb,hba⟩ := List.mem_map.1 hm
    have ha := head_mem a (he a (by simp))
    have hb' := head_mem b (he b (by simp [hb]))
    exact hh.2.2 _ ha _ (List.mem_flatten.2 ⟨b,hb,hb'⟩) hba.symm

theorem checked_monochromatic (S : Tree) (P : List (List Nat))
    (hp : partitionCheck (leaves S) P = true) :
    ∀ b, b ∈ P → LabelMonochromatic (blockColor P) b := by
  intro b hb x y hx hy
  rw [color_of_mem P (checked_flatten_nodup S P hp) b hb x hx,
    color_of_mem P (checked_flatten_nodup S P hp) b hb y hy]

/-- The executable representative labels are distinct realized colors and their
count is exactly the checked original block count. No rank field is assumed. -/
theorem checked_rank (S : Tree) (P : List (List Nat))
    (hp : partitionCheck (leaves S) P = true) : inputRank S (blockColor P) = P.length := by
  have hn := checked_flatten_nodup S P hp
  have he := partitionCheck_nonempty _ P hp
  have hrep := representative_nodup P hn he
  have hperm : (dedupNat ((leaves S).map (blockColor P))).Perm
      (P.map (fun b => b.headD 0)) := by
    apply (List.perm_ext_iff_of_nodup (dedupNat_nodup _) hrep).2
    intro i
    rw [mem_dedupNat]
    constructor
    · intro hi
      obtain ⟨x,hx,hxi⟩ := List.mem_map.1 hi
      obtain ⟨b,hb,hxb⟩ := Integration.partitionCheck_covers _ P hp x hx
      exact List.mem_map.2 ⟨b,hb,(color_of_mem P hn b hb x hxb).symm.trans hxi⟩
    · intro hi
      obtain ⟨b,hb,hbi⟩ := List.mem_map.1 hi
      have hh := head_mem b (he b hb)
      have hx := partitionCheck_subset _ P hp (List.mem_flatten.2 ⟨b,hb,hh⟩)
      exact List.mem_map.2 ⟨b.headD 0,hx,(color_of_mem P hn b hb _ hh).trans hbi⟩
  simpa only [inputRank,List.length_map] using hperm.length_eq

theorem checked_separation (S : Tree) (P : List (List Nat))
    (hp : partitionCheck (leaves S) P = true) (b : List Nat) (hb : b ∈ P) (x : Nat) :
    x ∈ b ↔ x ∈ leaves S ∧ blockColor P x = blockColor P (b.headD 0) := by
  exact rank_partition_color_classes S (blockColor P) P hp
    (checked_monochromatic S P hp) (checked_rank S P hp).symm b hb x

end Universal233.FinalCutRecovery
