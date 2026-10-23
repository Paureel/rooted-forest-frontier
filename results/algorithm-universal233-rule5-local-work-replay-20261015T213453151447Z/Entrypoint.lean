import Coverage
import CoreInvariants

/-! One-shot original-label input partition coverage at exact generate. -/
namespace Universal233.SourceCoverage
open RMAF CoreGraph CoreProgram Integration VertexGeometry

def RefinesBlocks (bs qs : List (List Nat)) : Prop :=
  ∀ b, b ∈ bs → ∃ a, a ∈ qs ∧ ∀ x, x ∈ b → x ∈ a

theorem partitionCheck_nonempty (labels : List Nat) (bs : List (List Nat))
    (hp : partitionCheck labels bs = true) (b : List Nat) (hb : b ∈ bs) : b ≠ [] := by
  have hn : bs.all (fun b => !b.isEmpty) = true := by
    simp only [partitionCheck,Bool.and_eq_true] at hp
    simp_all
  have h := List.all_eq_true.mp hn b hb
  simpa using h

theorem partitionCheck_subset (labels : List Nat) (bs : List (List Nat))
    (hp : partitionCheck labels bs = true) : bs.flatten ⊆ labels := by
  have hs : bs.flatten.all (fun x => labels.contains x) = true := by
    simp only [partitionCheck,Bool.and_eq_true] at hp
    exact hp.2
  intro x hx
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hs x hx)

theorem blocks_length_le_flatten (bs : List (List Nat))
    (hn : ∀ b, b ∈ bs → b ≠ []) : bs.length ≤ bs.flatten.length := by
  induction bs with
  | nil => simp
  | cons b rest ih =>
    have hb : 0 < b.length := List.length_pos_iff.mpr (hn b (by simp))
    have hr := ih (by intro a ha; exact hn a (by simp [ha]))
    simp only [List.length_cons,List.flatten_cons,List.length_append]
    omega

theorem partitionCheck_block_bound (labels : List Nat) (bs : List (List Nat))
    (hp : partitionCheck labels bs = true) : bs.length ≤ labels.length := by
  have hc : labels.all (fun x => bs.flatten.count x == 1) = true := by
    simp only [partitionCheck,Bool.and_eq_true] at hp
    simp_all
  have hs := partitionCheck_subset labels bs hp
  have hnd : bs.flatten.Nodup := by
    apply List.nodup_iff_count_of_mem.mpr
    intro x hx
    exact beq_iff_eq.mp (List.all_eq_true.mp hc x (hs hx))
  exact Nat.le_trans (blocks_length_le_flatten bs (partitionCheck_nonempty labels bs hp))
    (hnd.length_le_of_subset hs)

theorem leafAt_exists_of_mem (t : Tree) (x : Nat) (hx : x ∈ leaves t) :
    ∃ v, LeafAt t v x := by
  induction t with
  | leaf y => have he : x = y := by simpa [leaves] using hx
              subst x; exact ⟨[],rfl⟩
  | node l r ihl ihr =>
    simp only [leaves,List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨v,hv⟩ := ihl hx; exact ⟨false :: v,hv⟩
    · obtain ⟨v,hv⟩ := ihr hx; exact ⟨true :: v,hv⟩

theorem initial_ownerCover (t : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hp : partitionCheck (leaves t) bs = true) (he : pairwiseEmbeddings t bs = true) :
    OwnerCover (fromTree color [] t) (initialPartition t bs color hp he) (List.range bs.length) := by
  intro v g hv
  have hleaf := groupLeaf_skeleton (fromTree color [] t) v g hv
  rw [fromTree_skeleton] at hleaf
  obtain ⟨x,hx,hcolor⟩ := (recolor_leaf color t v g.color).mp hleaf
  obtain ⟨b,hb,hxb⟩ := partitionCheck_covers _ bs hp x (leafAt_label t v x hx)
  have ho := checkedOwner_at_support t bs he b hb v ((minimalVertices_terminal b t v x hx).mpr hxb)
  rw [initialPartition_owner,ho]
  exact List.mem_range.mpr (List.idxOf_lt_length_of_mem hb)

theorem initial_sourceRefines_blocks (t : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hp : partitionCheck (leaves t) bs = true) (he : pairwiseEmbeddings t bs = true)
    (blocks : List (List Nat))
    (hr : SourceRefines (fromTree color [] t) (initialPartition t bs color hp he) blocks) :
    RefinesBlocks bs blocks := by
  intro b hb
  have hbn := partitionCheck_nonempty (leaves t) bs hp b hb
  cases hbe : b with
  | nil => exact False.elim (hbn hbe)
  | cons x rest =>
    have hxb : x ∈ b := by simp [hbe]
    have hxt : x ∈ leaves t := partitionCheck_subset _ bs hp (List.mem_flatten.mpr ⟨b,hb,hxb⟩)
    obtain ⟨v,hv⟩ := leafAt_exists_of_mem t x hxt
    have hvg := fromTree_group_leaf color [] t v x hv
    obtain ⟨out,hout,hcover⟩ := hr v _ hvg
    refine ⟨out,hout,?_⟩
    intro y hy
    have hy : y ∈ b := by simpa only [hbe] using hy
    have hyt : y ∈ leaves t := partitionCheck_subset _ bs hp (List.mem_flatten.mpr ⟨b,hb,hy⟩)
    obtain ⟨w,hw⟩ := leafAt_exists_of_mem t y hyt
    have hwg := fromTree_group_leaf color [] t w y hw
    have ho : (initialPartition t bs color hp he).owner w = (initialPartition t bs color hp he).owner v := by
      change (checkedSourcePartition t bs hp he).owner w = (checkedSourcePartition t bs hp he).owner v
      exact (checkedSourcePartition_owner t bs hp he w v y x hw hv).mpr ⟨b,hb,hy,hxb⟩
    exact hcover w _ hwg ho y (by simp)

/-- Every source-valid monochromatic input partition survives in an ACTUAL
emitted output at the ordinary cut budget |bs|-1. Homogeneous contraction may
coarsen bs; the theorem preserves refinement by original taxon labels. -/
theorem generate_partition_coverage (t : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hnd : (leaves t).Nodup)
    (hp : partitionCheck (leaves t) bs = true) (he : pairwiseEmbeddings t bs = true)
    (hm : ∀ b, b ∈ bs → LabelMonochromatic color b)
    (q : Nat) (hq : bs.length - 1 ≤ q) :
    ∃ o, o ∈ (generate t color q).outputs ∧ RefinesBlocks bs o.partition := by
  let cap := min q ((leaves t).length - 1)
  have hcap : bs.length ≤ cap + 1 := by
    have hb := partitionCheck_block_bound (leaves t) bs hp
    dsimp [cap]
    omega
  obtain ⟨o,ho,hr,hkeep⟩ := run_coverage cap (fromTree color [] t) [] []
    (fromTree_origins_nodup color [] t) (fromTree_rootZeroOnly color t)
    (by intro v hv; simp at hv)
    (initialPartition t bs color hp he)
    (initialPartition_monochromatic t bs color hp he hm)
    (List.range bs.length) (initial_ownerCover t bs color hp he)
    (by simpa using hcap)
  refine ⟨o,?_,initial_sourceRefines_blocks t bs color hp he o.partition hr⟩
  simpa only [generate,ite_eq_left hnd,cap] using ho

end Universal233.SourceCoverage
