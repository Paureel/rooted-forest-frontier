import ColorClasses
import ResConsumers

/-! Fresh review seam. Source validity supplies only the original source check.
The reverse seam explicitly retains the independent original-target Q guard.
All costs count actual sourceCuts or literal local blocks. -/
namespace FreshRankRestrictionConsumer
open RMAF Universal233 Universal233.CoreProgram Universal233.SourceCoverage
open RestrictionBridge

theorem refinement_interface (F Q : List (List Nat)) :
    RefinesBlocks F Q ↔ RestrictionBridge.Refines F Q := by
  constructor <;> intro h B hB <;> obtain ⟨U,hU,hs⟩ := h B hB
  · exact ⟨U,hU,hs⟩
  · exact ⟨U,hU,hs⟩

/-- No target-Q embedding guard is needed in the forward direction. -/
theorem actual_output_forward (T S : Tree) (F : List (List Nat))
    (color : Nat → Nat) (q : Nat) (o : Output)
    (properT : (leaves T).Nodup) (properS : (leaves S).Nodup)
    (ho : o ∈ (generate S color q).outputs)
    (ha : agreement T S F = true) (href : RefinesBlocks F o.partition) :
    (∀ U ∈ o.partition, ∃ t s, restrict U T = some t ∧ restrict U S = some s ∧
      (leaves t).Perm U ∧ (leaves s).Perm U ∧ agreement t s (family U F) = true) ∧
    o.sourceCuts.length + (o.partition.map (fun U => (family U F).length - 1)).sum =
      F.length - 1 := by
  have hp := (Assembly.generated_source_valid S color q o ho).1
  have hr := (refinement_interface F o.partition).1 href
  have fw := forward_decomposition T S F o.partition properT properS ha hp hr
  have hpF : partitionCheck (leaves S) F = true := by
    simp only [agreement,Bool.and_eq_true] at ha
    exact ha.1.1.1.2
  have positive : ∀ U ∈ o.partition, 0 < (family U F).length := by
    intro U hU
    exact List.length_pos_iff.2 (family_nonempty (leaves S) F o.partition hpF hp hr U hU)
  have sumIdentity := sum_sub_one o.partition (fun U => (family U F).length) positive
  have total := total_family_length (leaves S) F o.partition hpF hp hr
  rw [total] at sumIdentity
  have cutIdentity := RankDichotomy.generate_partition_cost S color q o ho
  exact ⟨fw.1,by omega⟩

/-- Original target validity of Q is a genuine extra caller premise. -/
theorem actual_output_reverse (T S : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (G : List Nat → List (List Nat)) (t s : List Nat → Tree)
    (properT : (leaves T).Nodup) (properS : (leaves S).Nodup)
    (ho : o ∈ (generate S color q).outputs)
    (targetPartition : partitionCheck (leaves T) o.partition = true)
    (targetDisjoint : pairwiseEmbeddings T o.partition = true)
    (ht : ∀ U ∈ o.partition, restrict U T = some (t U))
    (hs : ∀ U ∈ o.partition, restrict U S = some (s U))
    (ha : ∀ U ∈ o.partition, agreement (t U) (s U) (G U) = true) :
    agreement T S (o.partition.flatMap G) = true ∧
    o.sourceCuts.length + (o.partition.map (fun U => (G U).length - 1)).sum =
      (o.partition.flatMap G).length - 1 := by
  have sourceValid := Assembly.generated_source_valid S color q o ho
  have rv := reverse_reconstruction T S o.partition G t s properT properS
    targetPartition sourceValid.1 targetDisjoint sourceValid.2 ht hs ha
  have positive : ∀ U ∈ o.partition, 0 < (G U).length := by
    intro U hU
    have local := ha U hU
    simp only [agreement,Bool.and_eq_true] at local
    have checked := local_checked_labels T (t U) U o.partition (G U)
      properT targetPartition hU (ht U hU) local.1.1.1.1
    exact List.length_pos_iff.2 (checked_family_nonempty U (G U)
      (checked_nonempty (leaves T) o.partition targetPartition U hU) checked)
  have sumIdentity := sum_sub_one o.partition (fun U => (G U).length) positive
  have flatIdentity : (o.partition.flatMap G).length =
      (o.partition.map (fun U => (G U).length)).sum := List.length_flatMap
  have cutIdentity := RankDichotomy.generate_partition_cost S color q o ho
  exact ⟨rv.1,by omega⟩

#print axioms refinement_interface
#print axioms actual_output_forward
#print axioms actual_output_reverse
end FreshRankRestrictionConsumer
