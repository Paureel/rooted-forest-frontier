import RationalMass
import Composition

/-! Whole-source ownership coloring: concrete parent tags and original target
regions. This module does not assume generator coverage in a structure field. -/
namespace Universal233.Assembly
open RMAF CoreProgram SourceCoverage VertexGeometry

def taggedColor (A B : List Nat) (ca cb cc : Nat → Nat) (x : Nat) : Nat :=
  if x ∈ A then 3 * ca x
  else if x ∈ B then 3 * cb x + 1 else 3 * cc x + 2

theorem tagged_same_parent (A B : List Nat) (ca cb cc : Nat → Nat) (x y : Nat)
    (h : taggedColor A B ca cb cc x = taggedColor A B ca cb cc y) :
    (x ∈ A ↔ y ∈ A) ∧ (x ∉ A → (x ∈ B ↔ y ∈ B)) := by
  unfold taggedColor at h
  by_cases hxa : x ∈ A <;> by_cases hya : y ∈ A <;>
    by_cases hxb : x ∈ B <;> by_cases hyb : y ∈ B <;>
    simp only [hxa,hya,hxb,hyb,ite_true,ite_false] at h <;>
    simp [hxa,hya,hxb,hyb] <;> omega

theorem tagged_mono_A (A B b : List Nat) (ca cb cc : Nat → Nat)
    (hs : ∀ x, x ∈ b → x ∈ A) (hm : LabelMonochromatic ca b) :
    LabelMonochromatic (taggedColor A B ca cb cc) b := by
  intro x y hx hy
  simp only [taggedColor,hs x hx,hs y hy,ite_true]
  exact congrArg (fun n => 3 * n) (hm x y hx hy)

theorem tagged_mono_B (A B b : List Nat) (ca cb cc : Nat → Nat)
    (hab : ∀ x, x ∈ A → x ∈ B → False)
    (hs : ∀ x, x ∈ b → x ∈ B) (hm : LabelMonochromatic cb b) :
    LabelMonochromatic (taggedColor A B ca cb cc) b := by
  intro x y hx hy
  have hnx : x ∉ A := fun ha => hab x ha (hs x hx)
  have hny : y ∉ A := fun ha => hab y ha (hs y hy)
  simp only [taggedColor,hnx,hny,hs x hx,hs y hy,ite_true,ite_false]
  exact congrArg (fun n => 3 * n + 1) (hm x y hx hy)

theorem tagged_mono_C (A B C b : List Nat) (ca cb cc : Nat → Nat)
    (hac : ∀ x, x ∈ A → x ∈ C → False)
    (hbc : ∀ x, x ∈ B → x ∈ C → False)
    (hs : ∀ x, x ∈ b → x ∈ C) (hm : LabelMonochromatic cc b) :
    LabelMonochromatic (taggedColor A B ca cb cc) b := by
  intro x y hx hy
  have hxa : x ∉ A := fun ha => hac x ha (hs x hx)
  have hya : y ∉ A := fun ha => hac y ha (hs y hy)
  have hxb : x ∉ B := fun hb => hbc x hb (hs x hx)
  have hyb : y ∉ B := fun hb => hbc y hb (hs y hy)
  simp only [taggedColor,hxa,hya,hxb,hyb,ite_false]
  exact congrArg (fun n => 3 * n + 2) (hm x y hx hy)

theorem tagged_original_partition_mono (A B C : List Nat)
    (F : List (List Nat)) (ca cb cc : Nat → Nat)
    (hab : ∀ x, x ∈ A → x ∈ B → False)
    (hac : ∀ x, x ∈ A → x ∈ C → False)
    (hbc : ∀ x, x ∈ B → x ∈ C → False)
    (hr : RefinesBlocks F [A,B,C])
    (ha : ∀ b, b ∈ F → (∀ x, x ∈ b → x ∈ A) → LabelMonochromatic ca b)
    (hb : ∀ b, b ∈ F → (∀ x, x ∈ b → x ∈ B) → LabelMonochromatic cb b)
    (hc : ∀ b, b ∈ F → (∀ x, x ∈ b → x ∈ C) → LabelMonochromatic cc b) :
    ∀ b, b ∈ F → LabelMonochromatic (taggedColor A B ca cb cc) b := by
  intro b hbf
  obtain ⟨p,hp,hs⟩ := hr b hbf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with hpa | hpb | hpc
  · have hsA : ∀ x, x ∈ b → x ∈ A := by simpa [hpa] using hs
    exact tagged_mono_A A B b ca cb cc hsA (ha b hbf hsA)
  · have hsB : ∀ x, x ∈ b → x ∈ B := by simpa [hpb] using hs
    exact tagged_mono_B A B b ca cb cc hab hsB (hb b hbf hsB)
  · have hsC : ∀ x, x ∈ b → x ∈ C := by simpa [hpc] using hs
    exact tagged_mono_C A B C b ca cb cc hac hbc hsC (hc b hbf hsC)

/-- Exact source-only parent tagging, using the ACTUAL generated output list. -/
theorem tagged_whole_source_coverage (source : Tree) (A B C : List Nat)
    (F : List (List Nat)) (ca cb cc : Nat → Nat)
    (hn : (leaves source).Nodup)
    (hp : partitionCheck (leaves source) F = true)
    (he : pairwiseEmbeddings source F = true)
    (hab : ∀ x, x ∈ A → x ∈ B → False)
    (hac : ∀ x, x ∈ A → x ∈ C → False)
    (hbc : ∀ x, x ∈ B → x ∈ C → False)
    (hr : RefinesBlocks F [A,B,C])
    (ha : ∀ b, b ∈ F → (∀ x, x ∈ b → x ∈ A) → LabelMonochromatic ca b)
    (hb : ∀ b, b ∈ F → (∀ x, x ∈ b → x ∈ B) → LabelMonochromatic cb b)
    (hc : ∀ b, b ∈ F → (∀ x, x ∈ b → x ∈ C) → LabelMonochromatic cc b)
    (q : Nat) (hq : F.length - 1 ≤ q) :
    ∃ o, o ∈ (generate source (taggedColor A B ca cb cc) q).outputs ∧
      RefinesBlocks F o.partition ∧ o.sourceCuts.length ≤ q := by
  exact generate_partition_coverage_paid source F (taggedColor A B ca cb cc)
    hn hp he (tagged_original_partition_mono A B C F ca cb cc hab hac hbc hr ha hb hc) q hq

/-- Clears in the unsuppressed ORIGINAL target imply actual whole-source
monochromaticity of the chosen parent's original final blocks. -/
theorem clear_parent_original_mono (target : Tree) (F : List (List Nat))
    (A : List Nat) (v : RMAF.Vertex)
    (hn : (leaves target).Nodup)
    (hp : partitionCheck (leaves target) F = true)
    (hinternal : ¬selectedLeaves (leaves target) target v)
    (hclear : ∀ b, b ∈ F → (∀ x, x ∈ b → x ∈ A) → v ∉ minimalVertices b target) :
    ∀ b, b ∈ F → (∀ x, x ∈ b → x ∈ A) →
      LabelMonochromatic (colorLabel target v) b := by
  intro b hb hs
  have hlabels : ∀ x, x ∈ b → x ∈ leaves target := by
    intro x hx
    exact partitionCheck_subset _ F hp (List.mem_flatten.mpr ⟨b,hb,hx⟩)
  have hno : ¬selectedLeaves b target v := by
    intro hv
    exact hinternal (selected_leaves_mono b (leaves target) target hlabels v hv)
  exact (original_label_avoids_iff target b v hn hlabels hno).1 (hclear b hb hs)

end Universal233.Assembly
