import CheapPartition
namespace Universal233.BinaryCheap
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly RankDichotomy RankConsumer

theorem pairwise_members (T : Tree) (F P : List (List Nat))
    (hn : F.flatten.Nodup) (hne : ∀ K, K ∈ F → K ≠ [])
    (hmap : ∀ K, K ∈ F → ∃ L, L ∈ P ∧ SameMembers K L)
    (hp : P.Pairwise (Disj T)) : F.Pairwise (Disj T) := by
  induction F with
  | nil => simp
  | cons K F ih =>
    have hflat := List.nodup_append.1 hn
    apply List.pairwise_cons.2
    constructor
    · intro L hL
      obtain ⟨U,hU,hKU⟩ := hmap K (by simp)
      obtain ⟨V,hV,hLV⟩ := hmap L (by simp [hL])
      have huv : U ≠ V := by
        intro he
        obtain ⟨x,hx⟩ := nonempty_witness K (hne K (by simp))
        have hxL : x ∈ L := (hLV x).2 (he ▸ (hKU x).1 hx)
        exact hflat.2.2 x hx x (List.mem_flatten.2 ⟨L,hL,hxL⟩) rfl
      exact disj_mono (pairwise_mem (fun _ _ => disj_symm) P hp U V hU hV huv)
        (fun x hx => (hKU x).1 hx) (fun x hx => (hLV x).1 hx)
    · exact ih hflat.2.1 (by intro L hL; exact hne L (by simp [hL]))
        (by intro L hL; exact hmap L (by simp [hL]))

/-- First actual graph consumer: the accepted rank4 A-clear core is exactly
[A_yes,A_no,B,C] up to block/label order, source-valid and target-disjoint.
No topology or paid-query conclusion is hidden in its premises. -/
theorem selected_accepted_partition (S T : Tree) (A B C : List Nat)
    (e : RMAF.Vertex × RMAF.Vertex)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x ∈ leaves S ↔ x ∈ leaves T)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hchoose : PairGeometry.choose T A B = some (.edge e))
    (hac : Disj T A C) (hbc : Disj T B C)
    (haccept : fourAccepted S (cheapColor A B (PairGeometry.descendants T e.2)) = true) :
    ∃ u o, treeAt T e.2 = some u ∧
      sideOutputs S B A (PairGeometry.descendants T e.2) 3 = [o] ∧
      o.sourceCuts.length = 3 ∧ o.partition.length = 4 ∧
      partitionCheck (leaves S) o.partition = true ∧ pairwiseEmbeddings S o.partition = true ∧
      pairwiseEmbeddings T o.partition = true ∧
      (∀ K, K ∈ o.partition → ∃ L, L ∈ classes A B C (leaves u) ∧ SameMembers K L) ∧
      (∀ L, L ∈ classes A B C (leaves u) → ∃ K, K ∈ o.partition ∧ SameMembers K L) ∧
      (∀ q, 3 ≤ q → sideOutputs S B A (PairGeometry.descendants T e.2) q = [o]) := by
  obtain ⟨u,hu,hay,han,hby,hbn,cay,can,cby,cbn,has,hbs⟩ := edge_facts T A B e hchoose
  have hcolor : cheapColor A B (PairGeometry.descendants T e.2) = cheapColor A B (leaves u) := by
    funext x
    simp only [cheapColor,WholeSourceMass.taggedColor,sideColor,FreshPairReview.descendants_treeAt T u e.2 ht hu x]
  rw [hcolor] at haccept
  obtain ⟨o,ho,hcost,hpart,hsource,hlen,hcl,hall⟩ := accepted_cheap S T A B C (leaves u) hs ht
    (fun x hx => (same x).1 hx) hp hay han haccept
  have hex := cheap_exact_classes S A B C (leaves u) o hp hay han hpart hcl
  have hm : o ∈ (generate S (cheapColor A B (leaves u)) 3).outputs := by change o ∈ sideOutputs S B A (leaves u) 3; rw [ho]; simp
  have hflat : o.partition.flatten.Nodup :=
    (CutRealization.generate_payload_perm S _ 3 o hm).symm.nodup (CutRealization.generate_finish_trace S _ 3 o hm).1
  have htarget : pairwiseEmbeddings T o.partition = true := by
    apply (executable_pairwiseEmbeddings T o.partition).2
    exact pairwise_members T o.partition _ hflat (partitionCheck_nonempty _ _ hpart) hex.1
      (classes_target T A B C (leaves u) has cay can hac hbc)
  have hout : ∀ q, sideOutputs S B A (PairGeometry.descendants T e.2) q = sideOutputs S B A (leaves u) q :=
    fun q => side_outputs_descendant S T u B A e.2 ht hu q
  exact ⟨u,o,hu,(hout 3).trans ho,hcost,hlen,hpart,hsource,htarget,hex.1,hex.2,
    fun q hq => (hout q).trans (hall q hq)⟩
end Universal233.BinaryCheap
