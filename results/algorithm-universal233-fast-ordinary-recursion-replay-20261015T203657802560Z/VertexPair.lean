import PairConsumer

namespace Universal233.PairAssembly
open RMAF CoreProgram SourceCoverage VertexGeometry PaidAssembly

def vertexPairOutputs (S T : Tree) (A B : List Nat) (v : RMAF.Vertex) (q : Nat) : List Output :=
  WholeSourceMass.wholeOutputs S A B (colorLabel T v) (fun _ => 0) (fun _ => 0) q ++
  WholeSourceMass.wholeOutputs S A B (fun _ => 0) (colorLabel T v) (fun _ => 0) q

def VertexPairClearing (T : Tree) (Q : List (List Nat)) (A B : List Nat) (v : RMAF.Vertex) : Prop :=
  Assembly.ParentClears T Q A (.at v) ∨ Assembly.ParentClears T Q B (.at v)

theorem overlap_internal (T : Tree) (A B : List Nat) (v : RMAF.Vertex)
    (hd : ∀ x, x ∈ A → x ∈ B → False)
    (hA : v ∈ minimalVertices A T) (hB : v ∈ minimalVertices B T) :
    ¬selectedLeaves (leaves T) T v := by
  have hn := disjoint_parent_overlap_nonlabel A B T v hd hA hB
  intro hs
  exact hn.1 (selected_leaf_reach_implies_self (leaves T) A T v hs
    (hull_subset_reach _ v ((minimalVertices_correct A T v).1 hA)))

theorem vertex_pair_cover (T S : Tree) (A B C : List Nat) (F : List (List Nat))
    (v : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    (hp : partitionCheck (leaves S) [A,B,C] = true) (hr : RefinesBlocks F [A,B,C])
    (hA : v ∈ minimalVertices A T) (hB : v ∈ minimalVertices B T)
    (hq : F.length-1 ≤ q) :
    ∃ o, o ∈ vertexPairOutputs S T A B v q ∧ OutputWitness S [A,B,C] F q o ∧
      VertexPairClearing T o.partition A B v := by
  obtain ⟨hab,hac,hbc⟩ := Assembly.parent_partition_disjoint S A B C hp
  have hi := overlap_internal T A B v hab hA hB
  have own := ownership_from_original_agreement T S F (Assembly.parentGroups F A B) hf
    (Assembly.parentGroups_belongs F A B) (Assembly.parentGroups_disjoint F A B)
  have both := two_parent_ownership_cover (PieceHulls T (Assembly.parentGroups F A B)) own 0 1 (by decide) v
  have build := Assembly.solution_from_requests T S A B C F
  rcases both with h | h
  · have clear := (pieceHulls_clear T (Assembly.parentGroups F A B) 0 v).1 h
    have sol := Assembly.branch_is_source_forest (build (.at v) .keep .keep q ht hs hl hf hp hab hac hbc hr
      (Assembly.internal_at T v hi) (Assembly.internal_keep T) (Assembly.internal_keep T)
      (Assembly.clears_A T F A B v clear) (Assembly.keeps_clear T F B) (Assembly.keeps_clear T F C) hq)
    obtain ⟨o,ho,hFQ,hQP,hpart,hemb,hreal,hbudget,ha,_,_⟩ := sol
    exact ⟨o,List.mem_append.mpr (Or.inl ho),⟨hFQ,hQP,hpart,hemb,hreal,hbudget⟩,Or.inl ha⟩
  · have clear := (pieceHulls_clear T (Assembly.parentGroups F A B) 1 v).1 h
    have sol := Assembly.branch_is_source_forest (build .keep (.at v) .keep q ht hs hl hf hp hab hac hbc hr
      (Assembly.internal_keep T) (Assembly.internal_at T v hi) (Assembly.internal_keep T)
      (Assembly.keeps_clear T F A) (Assembly.clears_B T F A B v hab clear) (Assembly.keeps_clear T F C) hq)
    obtain ⟨o,ho,hFQ,hQP,hpart,hemb,hreal,hbudget,_,hb,_⟩ := sol
    exact ⟨o,List.mem_append.mpr (Or.inr ho),⟨hFQ,hQP,hpart,hemb,hreal,hbudget⟩,Or.inr hb⟩

theorem vertex_pair_three_mass (S T : Tree) (A B C : List Nat) (v : RMAF.Vertex)
    (ht : (leaves T).Nodup) (hl : ∀ x, x ∈ leaves S → x ∈ leaves T)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hA : v ∈ minimalVertices A T) (hB : v ∈ minimalVertices B T)
    (hthree : (regions A T v).length=3 ∨ (regions B T v).length=3)
    (q : Nat) (c : Rat) (hc : 2 ≤ c) :
    rawQMass c (vertexPairOutputs S T A B v q) ≤ c^(-3 : Int)+c^(-4 : Int) := by
  have hm := partition_mass_interface S T A B C hp ht hl
  obtain ⟨ha,hb,_⟩ := WholeSourceMass.partition_target_support S T A B C hm.partition hl
  have hn := disjoint_parent_overlap_nonlabel A B T v hm.partition.ab hA hB
  have hca := WholeSourceMass.original_colors_at_least_two A T v ht ha hn.1 hA
  have hcb := WholeSourceMass.original_colors_at_least_two B T v ht hb hn.2 hB
  have hza := WholeSourceMass.localColors_zero A hm.aNonempty
  have hzb := WholeSourceMass.localColors_zero B hm.bNonempty
  have hzc := WholeSourceMass.localColors_zero C hm.cNonempty
  rcases hthree with hA3 | hB3
  · have h3 := (WholeSourceMass.original_colors_cardinality A T v ht ha hn.1).trans hA3
    have mA := WholeSourceMass.wholeOutputs_mass S A B C hm.partition (colorLabel T v)
      (fun _ => 0) (fun _ => 0) q 4 c hc (by omega)
    have mB := WholeSourceMass.wholeOutputs_mass S A B C hm.partition (fun _ => 0)
      (colorLabel T v) (fun _ => 0) q 3 c hc (by omega)
    have h := qadd_le_add mA mB
    simpa [vertexPairOutputs,WholeSourceMass.rawQMass_append,Rat.add_comm] using h
  · have h3 := (WholeSourceMass.original_colors_cardinality B T v ht hb hn.2).trans hB3
    have mA := WholeSourceMass.wholeOutputs_mass S A B C hm.partition (colorLabel T v)
      (fun _ => 0) (fun _ => 0) q 3 c hc (by omega)
    have mB := WholeSourceMass.wholeOutputs_mass S A B C hm.partition (fun _ => 0)
      (colorLabel T v) (fun _ => 0) q 4 c hc (by omega)
    have h := qadd_le_add mA mB
    simpa [vertexPairOutputs,WholeSourceMass.rawQMass_append] using h
end Universal233.PairAssembly
