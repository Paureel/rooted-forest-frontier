import ValidPartition
import RationalMass
namespace FreshCompletionReview
open RMAF Universal233 CoreProgram

theorem distinctColorCounts (t : Tree) (color : Nat → Nat) :
    CutRealization.colorCount t color =
      (SourceCoverage.dedupNat ((leaves t).map color)).length := by
  unfold CutRealization.colorCount
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup (CutRealization.color_dedup_nodup _)
    (SourceCoverage.dedupNat_nodup _)).mpr
  intro x
  simp only [List.mem_eraseDups,SourceCoverage.mem_dedupNat]

theorem every_actual_output (t : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate t color q).outputs) :
    CutRealization.RealizedOutput t o ∧ partitionCheck (leaves t) o.partition = true ∧
    (∀ b, b ∈ o.partition → VertexGeometry.LabelMonochromatic color b) ∧
    (SourceCoverage.dedupNat ((leaves t).map color)).length - 1 ≤ o.sourceCuts.length ∧
    o.sourceCuts.length ≤ min q ((leaves t).length - 1) := by
  refine ⟨CutRealization.generate_original_realization t color q o ho,
    CutRealization.generate_partition_check t color q o ho,
    CutRealization.generate_monochromatic t color q o ho,?_,
    SourceCoverage.generate_output_cap t color q o ho⟩
  rw [←distinctColorCounts]
  exact CutRealization.generate_realized_color_cost t color q o ho

/-- Nonauthor consuming call: the refinement witness belongs to the same
literal output list whose ALL members have actual original cuts and whose
RAW list mass is bounded. No runtime, target-tree or solver assertion. -/
theorem completed_source_consumer (t : Tree) (bs : List (List Nat))
    (color : Nat → Nat) (q : Nat)
    (hn : (leaves t).Nodup)
    (hp : partitionCheck (leaves t) bs = true)
    (he : pairwiseEmbeddings t bs = true)
    (hm : ∀ b, b ∈ bs → VertexGeometry.LabelMonochromatic color b)
    (hq : bs.length - 1 ≤ q) (c : Rat) (hc : 2 ≤ c) :
    (∃ o, o ∈ (generate t color q).outputs ∧
      SourceCoverage.RefinesBlocks bs o.partition ∧
      CutRealization.RealizedOutput t o ∧
      partitionCheck (leaves t) o.partition = true ∧
      (∀ b, b ∈ o.partition → VertexGeometry.LabelMonochromatic color b) ∧
      (SourceCoverage.dedupNat ((leaves t).map color)).length - 1 ≤ o.sourceCuts.length ∧
      o.sourceCuts.length ≤ min q ((leaves t).length - 1)) ∧
    SourceCoverage.rawQMass c (generate t color q).outputs ≤
      c ^ (1 - ((SourceCoverage.dedupNat ((leaves t).map color)).length : Int)) := by
  constructor
  · obtain ⟨o,ho,href,hpaid⟩ :=
      SourceCoverage.generate_partition_coverage_paid t bs color hn hp he hm q hq
    exact ⟨o,ho,href,every_actual_output t color q o ho⟩
  · exact SourceCoverage.generate_rawQ_mass t color q c hc

example (t : Tree) (color : Nat → Nat) (q : Nat) :
    SourceCoverage.rawQMass (233/100) (generate t color q).outputs ≤
      (233/100 : Rat) ^ (1 - ((SourceCoverage.dedupNat ((leaves t).map color)).length : Int)) :=
  SourceCoverage.generate_rawQ_mass t color q (233/100) (by decide +kernel)
end FreshCompletionReview
