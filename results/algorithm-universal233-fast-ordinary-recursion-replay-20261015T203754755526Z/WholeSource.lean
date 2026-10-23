import ParentColors
import ValidPartition

namespace Universal233.Assembly
open RMAF CoreProgram SourceCoverage VertexGeometry

theorem parent_cover (source : Tree) (A B C : List Nat)
    (hp : partitionCheck (leaves source) [A,B,C] = true)
    (x : Nat) (hx : x ∈ leaves source) : x ∈ A ∨ x ∈ B ∨ x ∈ C := by
  obtain ⟨b,hb,hxb⟩ := Integration.partitionCheck_covers _ [A,B,C] hp x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with hb | hb | hb
  · exact Or.inl (hb ▸ hxb)
  · exact Or.inr (Or.inl (hb ▸ hxb))
  · exact Or.inr (Or.inr (hb ▸ hxb))

/-- All actual output blocks remain inside one original hard parent because
parent tags are part of the concrete color, including after suppression. -/
theorem tagged_output_refines_parents (source : Tree) (A B C : List Nat)
    (ca cb cc : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate source (taggedColor A B ca cb cc) q).outputs)
    (hp : partitionCheck (leaves source) [A,B,C] = true)
    (hab : ∀ x, x ∈ A → x ∈ B → False)
    (hac : ∀ x, x ∈ A → x ∈ C → False)
    (hbc : ∀ x, x ∈ B → x ∈ C → False) :
    RefinesBlocks o.partition [A,B,C] := by
  have hq := CutRealization.generate_partition_check source _ q o ho
  have hmono := CutRealization.generate_monochromatic source _ q o ho
  intro b hb
  have hn := partitionCheck_nonempty (leaves source) o.partition hq b hb
  obtain ⟨x,hx⟩ : ∃ x, x ∈ b := by
    cases b with
    | nil => exact False.elim (hn rfl)
    | cons x xs => exact ⟨x,by simp⟩
  have inSource : ∀ y, y ∈ b → y ∈ leaves source := by
    intro y hy
    exact partitionCheck_subset _ o.partition hq (List.mem_flatten.mpr ⟨b,hb,hy⟩)
  rcases parent_cover source A B C hp x (inSource x hx) with hxa | hxb | hxc
  · refine ⟨A,by simp,?_⟩
    intro y hy
    exact (tagged_same_parent A B ca cb cc x y (hmono b hb x y hx hy)).1.mp hxa
  · have hnx : x ∉ A := fun ha => hab x ha hxb
    refine ⟨B,by simp,?_⟩
    intro y hy
    exact ((tagged_same_parent A B ca cb cc x y (hmono b hb x y hx hy)).2 hnx).mp hxb
  · have hxa : x ∉ A := fun ha => hac x ha hxc
    have hxb : x ∉ B := fun hb => hbc x hb hxc
    refine ⟨C,by simp,?_⟩
    intro y hy
    have same := tagged_same_parent A B ca cb cc x y (hmono b hb x y hx hy)
    rcases parent_cover source A B C hp y (inSource y hy) with hya | hyb | hyc
    · exact False.elim (hxa (same.1.mpr hya))
    · exact False.elim (hxb ((same.2 hxa).mpr hyb))
    · exact hyc

/-- A selected parent's actual output pieces clear the required original
target vertex, by their actual computed color, not a supplied coverage field. -/
theorem tagged_output_clears_A (target source : Tree) (A B : List Nat)
    (cb cc : Nat → Nat) (v : RMAF.Vertex) (q : Nat) (o : Output)
    (ho : o ∈ (generate source (taggedColor A B (colorLabel target v) cb cc) q).outputs)
    (ht : (leaves target).Nodup)
    (hlabels : ∀ x, x ∈ leaves source → x ∈ leaves target)
    (hinternal : ¬selectedLeaves (leaves target) target v) :
    ∀ b, b ∈ o.partition → (∀ x, x ∈ b → x ∈ A) → v ∉ minimalVertices b target := by
  have hq := CutRealization.generate_partition_check source _ q o ho
  have hmono := CutRealization.generate_monochromatic source _ q o ho
  intro b hb hs
  have hm : LabelMonochromatic (colorLabel target v) b := by
    intro x y hx hy
    have hh := hmono b hb x y hx hy
    simp only [taggedColor,hs x hx,hs y hy,ite_true] at hh
    omega
  have hvalid : ∀ x, x ∈ b → x ∈ leaves target := by
    intro x hx
    exact hlabels x (partitionCheck_subset _ o.partition hq (List.mem_flatten.mpr ⟨b,hb,hx⟩))
  have hno : ¬selectedLeaves b target v := by
    intro hv
    exact hinternal (selected_leaves_mono b (leaves target) target hvalid v hv)
  exact (original_label_avoids_iff target b v ht hvalid hno).2 hm

/-- Whole-source generated ownership branch, with original refinement,
actual original cuts, parent containment and original target clearing. -/
theorem clear_A_whole_source (target source : Tree) (A B C : List Nat)
    (F : List (List Nat)) (v : RMAF.Vertex) (q : Nat)
    (ht : (leaves target).Nodup) (hs : (leaves source).Nodup)
    (hlabels : ∀ x, x ∈ leaves source → x ∈ leaves target)
    (hpt : partitionCheck (leaves target) F = true)
    (hps : partitionCheck (leaves source) F = true)
    (hes : pairwiseEmbeddings source F = true)
    (hpp : partitionCheck (leaves source) [A,B,C] = true)
    (hab : ∀ x, x ∈ A → x ∈ B → False)
    (hac : ∀ x, x ∈ A → x ∈ C → False)
    (hbc : ∀ x, x ∈ B → x ∈ C → False)
    (hfp : RefinesBlocks F [A,B,C])
    (hinternal : ¬selectedLeaves (leaves target) target v)
    (hclear : ∀ b, b ∈ F → (∀ x, x ∈ b → x ∈ A) → v ∉ minimalVertices b target)
    (hq : F.length - 1 ≤ q) :
    ∃ o, o ∈ (generate source
          (taggedColor A B (colorLabel target v) (fun _ => 0) (fun _ => 0)) q).outputs ∧
      RefinesBlocks F o.partition ∧ RefinesBlocks o.partition [A,B,C] ∧
      partitionCheck (leaves source) o.partition = true ∧
      CutRealization.RealizedOutput source o ∧ o.sourceCuts.length ≤ q ∧
      (∀ b, b ∈ o.partition → (∀ x, x ∈ b → x ∈ A) → v ∉ minimalVertices b target) := by
  have hma := clear_parent_original_mono target F A v ht hpt hinternal hclear
  have zero : ∀ b : List Nat, LabelMonochromatic (fun _ => 0) b := by intros b x y hx hy; rfl
  obtain ⟨o,ho,href,hbudget⟩ := tagged_whole_source_coverage source A B C F
    (colorLabel target v) (fun _ => 0) (fun _ => 0) hs hps hes hab hac hbc hfp hma
    (fun b _ _ => zero b) (fun b _ _ => zero b) q hq
  exact ⟨o,ho,href,tagged_output_refines_parents source A B C _ _ _ q o ho hpp hab hac hbc,
    CutRealization.generate_partition_check source _ q o ho,
    CutRealization.generate_original_realization source _ q o ho,hbudget,
    tagged_output_clears_A target source A B _ _ v q o ho ht hlabels hinternal⟩

end Universal233.Assembly
