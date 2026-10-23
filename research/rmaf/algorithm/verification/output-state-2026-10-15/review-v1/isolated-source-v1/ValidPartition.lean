import Cost

namespace Universal233.CutRealization
open RMAF CoreGraph CoreProgram Integration List

def wholePayload (t : GTree) (d : List Group) : List Nat :=
  d.flatMap Group.labels ++ payload t

theorem History.whole_payload {T color t d c} (h : History T color t d c)
    (hn : (leaves T).Nodup) : (wholePayload t d).Perm (leaves T) := by
  induction h with
  | initial => simp [wholePayload,fromTree_payload]
  | normalized h ih => simpa only [wholePayload,normalize_payload] using ih
  | @detached t d c next v g h hv hvr hgr hgc he ih =>
    obtain ⟨u,hu,⟨e⟩⟩ := erase_leaf_realization t (h.invariant hn).originNodup v g hv hvr
    have eu : u = next := Option.some.inj (hu.symm.trans he)
    subst u
    have one := List.Perm.append_left (d.flatMap Group.labels) (gleaf_payload_perm e)
    have two := (List.perm_append_comm (l₁ := d.flatMap Group.labels) (l₂ := g.labels)).append_right (payload next)
    have hh : (wholePayload t d).Perm (wholePayload next (g :: d)) :=
      one.trans (by simpa [wholePayload,List.append_assoc] using two)
    exact hh.symm.trans ih

theorem generate_payload_perm (T : Tree) (color : Nat → Nat) (budget : Nat) (o : Output)
    (ho : o ∈ (generate T color budget).outputs) : o.partition.flatten.Perm (leaves T) := by
  obtain ⟨hn,t,d,c,hh,hfinish,he⟩ := generate_finish_trace T color budget o ho
  subst o
  simpa [wholePayload,List.flatMap,payload_groups] using hh.whole_payload hn

/-- Literal output list satisfies the ordinary executable partition checker. -/
theorem generate_partition_check (T : Tree) (color : Nat → Nat) (budget : Nat) (o : Output)
    (ho : o ∈ (generate T color budget).outputs) : partitionCheck (leaves T) o.partition = true := by
  have hr := generate_original_realization T color budget o ho
  have hp := generate_payload_perm T color budget o ho
  have hn := (generate_finish_trace T color budget o ho).1
  have hnd := hp.symm.nodup hn
  simp only [partitionCheck,Bool.and_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply List.all_eq_true.2
    intro b hb
    have hne := realized_blocks_nonempty hr b hb
    cases b <;> simp_all
  · apply List.all_eq_true.2
    intro x hx
    have hmem : x ∈ o.partition.flatten := hp.mem_iff.2 hx
    have hcount : o.partition.flatten.count x = 1 := (List.nodup_iff_count_of_mem.1 hnd) x hmem
    simpa only [beq_iff_eq] using hcount
  · apply List.all_eq_true.2
    intro x hx
    exact List.contains_iff_mem.2 (hp.mem_iff.1 hx)

theorem checked_source_core (T : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hn : (leaves T).Nodup) (hp : partitionCheck (leaves T) bs = true)
    (he : pairwiseEmbeddings T bs = true)
    (hm : ∀ b, b ∈ bs → VertexGeometry.LabelMonochromatic color b) :
    ∃ o, o ∈ (generate T color (bs.length - 1)).outputs ∧
      partitionCheck (leaves T) o.partition = true ∧
      VertexGeometry.Refines bs o.partition ∧ RealizedOutput T o ∧
      (∀ b, b ∈ o.partition → VertexGeometry.LabelMonochromatic color b) ∧
      colorCount T color - 1 ≤ o.sourceCuts.length ∧ o.sourceCuts.length ≤ bs.length - 1 := by
  obtain ⟨o,ho,href,hreal,hmono,hlo,hhi⟩ := source_core T bs color hn hp he hm
  exact ⟨o,ho,generate_partition_check T color _ o ho,href,hreal,hmono,hlo,hhi⟩

end Universal233.CutRealization
