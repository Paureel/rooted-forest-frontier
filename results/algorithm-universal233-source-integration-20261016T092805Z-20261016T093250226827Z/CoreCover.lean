import Crossing
namespace Universal233.BothBad
open RMAF CoreProgram SourceCoverage VertexGeometry PairAssembly PaidAssembly

theorem swap_refinement (F : List (List Nat)) (A B C : List Nat)
    (h : RefinesBlocks F [A,B,C]) : RefinesBlocks F [B,A,C] := by
  intro K hK
  obtain ⟨U,hU,hsub⟩ := h K hK
  exact ⟨U,by simpa [or_comm,or_left_comm,or_assoc] using hU,hsub⟩

theorem side_core_cover (S : Tree) (A B C D : List Nat) (F : List (List Nat))
    (hs : (leaves S).Nodup) (hF : partitionCheck (leaves S) F=true)
    (hEmb : pairwiseEmbeddings S F=true) (hp : partitionCheck (leaves S) [A,B,C]=true)
    (hr : RefinesBlocks F [A,B,C])
    (hm : ∀ K∈F, (∀ x, x∈K → x∈B) → LabelMonochromatic (sideColor D) K)
    (q : Nat) (hq : F.length-1≤q) :
    ∃ o, o∈sideOutputs S A B D q ∧ OutputWitness S [A,B,C] F q o := by
  obtain ⟨hab,hac,hbc⟩ := Assembly.parent_partition_disjoint S A B C hp
  obtain ⟨o,ho,hFQ,hbudget⟩ := Assembly.tagged_whole_source_coverage S A B C F
    (fun _ => 0) (sideColor D) (fun _ => 0) hs hF hEmb hab hac hbc hr
    (by intro K hK hKA x y hx hy; rfl) hm (by intro K hK hKC x y hx hy; rfl) q hq
  have hvalid := Assembly.generated_source_valid S _ q o ho
  exact ⟨o,ho,hFQ,Assembly.tagged_output_refines_parents S A B C _ _ _ q o ho hp hab hac hbc,
    hvalid.1,hvalid.2,CutRealization.generate_original_realization S _ q o ho,hbudget⟩

/-- Two actual source-core LISTS cover every original agreement refining the
    three source parents. The proof uses original vertex ownership and the
    actual selected edge; no emitted-coverage field or target-Q disjointness. -/
theorem selected_binary_core_cover (S T : Tree) (A B C : List Nat)
    (e : RMAF.Vertex × RMAF.Vertex) (F : List (List Nat))
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (hchoose : PairGeometry.choose T A B=some (.edge e))
    (hF : agreement T S F=true) (hr : RefinesBlocks F [A,B,C])
    (q : Nat) (hq : F.length-1≤q) :
    ∃ o, o∈outputs S A B (PairGeometry.descendants T e.2) q ∧
      OutputWitness S [A,B,C] F q o := by
  have hsource : partitionCheck (leaves S) F=true := by
    have hh:=hF; simp only [agreement,Bool.and_eq_true] at hh; exact hh.1.1.1.2
  have hEmb := (agreement_graph_factors T S F hF).2.1
  have hab := (Assembly.parent_partition_disjoint S A B C hp).1
  obtain ⟨_,hvalid⟩ := PairGeometry.choose_sound T A B (.edge e) hchoose
  obtain ⟨p,s,he⟩ := PairGeometry.edges_shape T e hvalid.1
  subst e
  rcases original_binary_parent_mono T S F A B p s ht hF hab with hA | hB
  · obtain ⟨o,ho,hout⟩ := side_core_cover S B A C (PairGeometry.descendants T (p++[s])) F
      hs hsource hEmb (BinaryCheap.partition_swap _ A B C hp) (swap_refinement F A B C hr) hA q hq
    obtain ⟨hFQ,hQP,hpart,hsourceQ,hreal,hbudget⟩ := hout
    exact ⟨o,List.mem_append.2 (Or.inl ho),hFQ,swap_refinement _ B A C hQP,hpart,hsourceQ,hreal,hbudget⟩
  · obtain ⟨o,ho,hout⟩ := side_core_cover S A B C (PairGeometry.descendants T (p++[s])) F
      hs hsource hEmb hp hr hB q hq
    exact ⟨o,List.mem_append.2 (Or.inr ho),hout⟩
end Universal233.BothBad
