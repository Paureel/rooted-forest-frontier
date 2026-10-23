import TailMass

namespace Universal233.RankDichotomy
open RMAF CoreProgram SourceCoverage VertexGeometry

theorem dedupNat_length_le (xs : List Nat) : (dedupNat xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [dedupNat]
  | cons x xs ih => simp only [dedupNat]; split <;> simp_all <;> omega

theorem nodup_of_dedupNat_length (xs : List Nat)
    (h : (dedupNat xs).length = xs.length) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hlo := dedupNat_length_le xs
      simp only [dedupNat] at h
      split at h
      · simp only [List.length_cons] at h; omega
      · rename_i hn
        have hlen : (dedupNat xs).length = xs.length := by simpa using h
        exact List.nodup_cons.mpr ⟨fun hx => hn ((mem_dedupNat xs x).mpr hx),ih hlen⟩

theorem nodup_map_injective {α β : Type} (bs : List α) (f : α → β)
    (hn : (bs.map f).Nodup) (b c : α) (hb : b ∈ bs) (hc : c ∈ bs)
    (he : f b = f c) : b = c := by
  induction bs with
  | nil => simp at hb
  | cons a bs ih =>
      have hn' := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hb with hba | hbt
      · subst b
        rcases List.mem_cons.mp hc with hca | hct
        · exact hca.symm
        · exact False.elim (hn'.1 (List.mem_map.mpr ⟨c,hct,he.symm⟩))
      · rcases List.mem_cons.mp hc with hca | hct
        · subst c
          exact False.elim (hn'.1 (List.mem_map.mpr ⟨b,hbt,he⟩))
        · exact ih hn'.2 hbt hct

theorem rank_representatives_nodup (T : Tree) (color : Nat → Nat) (bs : List (List Nat))
    (hp : partitionCheck (leaves T) bs = true)
    (hm : ∀ b, b ∈ bs → LabelMonochromatic color b)
    (hlen : bs.length = inputRank T color) :
    (bs.map (fun b => color (b.headD 0))).Nodup := by
  let cs := bs.map (fun b => color (b.headD 0))
  have hsub : dedupNat ((leaves T).map color) ⊆ dedupNat cs := by
    intro i hi
    obtain ⟨x,hx,hxi⟩ := List.mem_map.mp ((mem_dedupNat _ i).mp hi)
    obtain ⟨b,hb,hxb⟩ := Integration.partitionCheck_covers _ bs hp x hx
    have hne := partitionCheck_nonempty _ bs hp b hb
    have hh : b.headD 0 ∈ b := by cases b <;> simp_all
    exact (mem_dedupNat cs i).mpr (List.mem_map.mpr ⟨b,hb,(hm b hb x _ hxb hh).symm.trans hxi⟩)
  have hlo := (dedupNat_nodup ((leaves T).map color)).length_le_of_subset hsub
  have hhi := dedupNat_length_le cs
  have hc : cs.length = inputRank T color := by simpa only [cs,List.length_map] using hlen
  have he : (dedupNat cs).length = cs.length := by change inputRank T color ≤ _ at hlo; omega
  exact nodup_of_dedupNat_length cs he

/-- Every rank-r monochromatic checked partition contains each realized color
as precisely one whole original-label class. This is membership equality, with
no order or original cut-address normalization imposed. -/
theorem rank_partition_color_classes (T : Tree) (color : Nat → Nat) (bs : List (List Nat))
    (hp : partitionCheck (leaves T) bs = true)
    (hm : ∀ b, b ∈ bs → LabelMonochromatic color b)
    (hlen : bs.length = inputRank T color) (b : List Nat) (hb : b ∈ bs) (y : Nat) :
    y ∈ b ↔ y ∈ leaves T ∧ color y = color (b.headD 0) := by
  have hne := partitionCheck_nonempty _ bs hp b hb
  have hh : b.headD 0 ∈ b := by cases b <;> simp_all
  constructor
  · intro hy
    exact ⟨partitionCheck_subset _ bs hp (List.mem_flatten.mpr ⟨b,hb,hy⟩),hm b hb y _ hy hh⟩
  · rintro ⟨hy,hcol⟩
    obtain ⟨c,hc,hyc⟩ := Integration.partitionCheck_covers _ bs hp y hy
    have hnc := partitionCheck_nonempty _ bs hp c hc
    have hhc : c.headD 0 ∈ c := by cases c <;> simp_all
    have hecol : color (b.headD 0) = color (c.headD 0) :=
      hcol.symm.trans (hm c hc y _ hyc hhc)
    have he := nodup_map_injective bs (fun b => color (b.headD 0))
      (rank_representatives_nodup T color bs hp hm hlen) b c hb hc hecol
    simpa only [he] using hyc

theorem feasible_unique_color_classes (T : Tree) (color : Nat → Nat) (hn : (leaves T).Nodup)
    (hf : RankFeasible T color) (q : Nat) (hq : inputRank T color - 1 ≤ q) :
    ∃ o, (generate T color q).outputs = [o] ∧ o.sourceCuts.length = inputRank T color - 1 ∧
      ∀ b, b ∈ o.partition → ∀ y, y ∈ b ↔ y ∈ leaves T ∧ color y = color (b.headD 0) := by
  obtain ⟨o,ho,hpaid⟩ := feasible_unique T color hn hf q hq
  have hmem : o ∈ (generate T color q).outputs := by rw [ho]; simp
  have hp := CutRealization.generate_partition_check T color q o hmem
  have hm := CutRealization.generate_monochromatic T color q o hmem
  have hlen := generate_partition_cost T color q o hmem
  have hr := inputRank_pos T color
  refine ⟨o,ho,hpaid,?_⟩
  intro b hb y
  exact rank_partition_color_classes T color o.partition hp hm (by omega) b hb y

end Universal233.RankDichotomy
