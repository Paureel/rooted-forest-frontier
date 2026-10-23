import SideColors

namespace Universal233.PairAssembly
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PaidAssembly

theorem kept_parent_of_refinement (S T : Tree) (A B C : List Nat)
    (F Q : List (List Nat))
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hA : A ∈ F) (hFQ : RefinesBlocks F Q) (hQP : RefinesBlocks Q [A,B,C])
    (hgood : restrictionAgrees S T A = true) :
    ∃ K, K ∈ Q ∧ (∀ x, x ∈ K ↔ x ∈ A) ∧ restrictionAgrees S T K = true := by
  obtain ⟨hab,hac,_⟩ := Assembly.parent_partition_disjoint S A B C hp
  obtain ⟨x,hx⟩ := nonempty_witness A (partitionCheck_nonempty _ _ hp A (by simp))
  obtain ⟨K,hK,hAK⟩ := hFQ A hA
  obtain ⟨P,hP,hKP⟩ := hQP K hK
  have hKA : Sub K A := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hP
    rcases hP with rfl | rfl | rfl
    · exact hKP
    · exact False.elim (hab x hx (hKP x (hAK x hx)))
    · exact False.elim (hac x hx (hKP x (hAK x hx)))
  have he : ∀ x, x ∈ K ↔ x ∈ A := fun x => ⟨hKA x,hAK x⟩
  refine ⟨K,hK,he,?_⟩
  have hS := restrict_congr S K A (fun x _ => he x)
  have hT := restrict_congr T K A (fun x _ => he x)
  simpa only [restrictionAgrees,hS,hT] using hgood

/-- Executable branch computes only the side-colored source core. E is used
in this proof to obtain an actual no-larger agreement F'; it is not an oracle
or an operation executed on an unknown final forest. -/
theorem selected_edge_good_parent_core (S T : Tree) (A B C : List Nat)
    (e : RMAF.Vertex × RMAF.Vertex) (F : List (List Nat)) (q : Nat)
    (hs : (leaves S).Nodup) (sameLabels : ∀ x, x ∈ leaves S ↔ x ∈ leaves T)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hsource : pairwiseEmbeddings S [A,B,C] = true)
    (hAB : A ≠ B) (hchoose : PairGeometry.choose T A B = some (.edge e))
    (clearOther : ∀ E, E ∈ [A,B,C] → E ≠ A → E ≠ B → Disj T E A ∧ Disj T E B)
    (hgood : restrictionAgrees S T A = true)
    (hF : agreement S T F = true) (hFP : RefinesBlocks F [A,B,C])
    (hq : F.length-1 ≤ q) (c : Rat) (hc : 2 ≤ c) :
    ∃ u F' o, treeAt T e.2 = some u ∧ F' = exchange A B F u ∧
      agreement S T F' = true ∧ RefinesBlocks F' [A,B,C] ∧ F'.length ≤ F.length ∧
      o ∈ sideOutputs S A B (leaves u) q ∧ OutputWitness S [A,B,C] F' q o ∧
      (∀ K, K ∈ o.partition → Sub K B → Disj T K A) ∧
      (∃ K, K ∈ o.partition ∧ (∀ x, x ∈ K ↔ x ∈ A) ∧ restrictionAgrees S T K = true) ∧
      (dedupNat ((leaves S).map (WholeSourceMass.taggedColor A B (fun _ => 0) (sideColor (leaves u)) (fun _ => 0)))).length = 4 ∧
      rawQMass c (sideOutputs S A B (leaves u) q) ≤ c^(-3 : Int) := by
  obtain ⟨hproper,hvalid⟩ := PairGeometry.choose_sound T A B (.edge e) hchoose
  have ht := PairGeometry.proper_nodup T A B hproper
  have hl : ∀ x, x ∈ leaves S → x ∈ leaves T := fun x hx => (sameLabels x).1 hx
  obtain ⟨u,hu,hEx⟩ := FreshPairReview.selector_edge_exchange S T [A,B,C] A B e hs sameLabels hp hsource
    (by simp) (by simp) hAB hchoose clearOther hgood F hF hFP
  dsimp only at hEx
  let F' := exchange A B F u
  change agreement S T F' = true ∧ RefinesBlocks F' [A,B,C] ∧ F'.count A = 1 ∧
    (∀ K, K ∈ F' → Sub K B → (∀ x, x ∈ K → x ∈ leaves u) ∨ (∀ x, x ∈ K → x ∉ leaves u)) ∧
    F'.length ≤ F.length ∧ outside A B F' = outside A B F at hEx
  obtain ⟨hAF,hRef,hCount,hMono,hLen,_⟩ := hEx
  have hq' : F'.length-1 ≤ q := Nat.le_trans (Nat.sub_le_sub_right hLen 1) hq
  have hparts := hAF
  simp only [agreement,Bool.and_eq_true] at hparts
  have hps : partitionCheck (leaves S) F' = true := hparts.1.1.1.1
  have hes : pairwiseEmbeddings S F' = true := hparts.1.2
  obtain ⟨hab,hac,hbc⟩ := Assembly.parent_partition_disjoint S A B C hp
  have hKeep : ∀ K, K ∈ F' → (∀ x, x ∈ K → x ∈ A) → LabelMonochromatic (fun _ => 0) K := by
    intros; intro x y hx hy; rfl
  have hKeepC : ∀ K, K ∈ F' → (∀ x, x ∈ K → x ∈ C) → LabelMonochromatic (fun _ => 0) K := by
    intros; intro x y hx hy; rfl
  have hSide : ∀ K, K ∈ F' → (∀ x, x ∈ K → x ∈ B) → LabelMonochromatic (sideColor (leaves u)) K := by
    intro K hK hKB
    exact side_mono_of_sector (leaves u) K (hMono K hK hKB)
  obtain ⟨o,ho,hFQ,hBudget⟩ := Assembly.tagged_whole_source_coverage S A B C F'
    (fun _ => 0) (sideColor (leaves u)) (fun _ => 0) hs hps hes hab hac hbc hRef hKeep hSide hKeepC q hq'
  have hQRef := Assembly.tagged_output_refines_parents S A B C _ _ _ q o ho hp hab hac hbc
  have hQ := Assembly.generated_source_valid S _ q o ho
  have hReal := CutRealization.generate_original_realization S _ q o ho
  change e ∈ PairGeometry.edges T ∧ e.1 ∈ minimalVertices A T ∧ e.1 ∈ minimalVertices B T ∧
    e.2 ∈ minimalVertices A T ∧ e.2 ∈ minimalVertices B T ∧
    (∀ i, PairGeometry.sideLabels A T e.2 i ≠ []) ∧
    (∀ i, PairGeometry.sideLabels B T e.2 i ≠ []) ∧ PairGeometry.ActualClear T A B e.2 at hvalid
  obtain ⟨_,_,_,_,_,_,hBs,hClear⟩ := hvalid
  have hBy : yes B ((leaves u).contains ·) ≠ [] := by
    rw [←FreshPairReview.side_yes B T u e.2 ht hu]; exact hBs true
  have hBn : no B ((leaves u).contains ·) ≠ [] := by
    rw [←FreshPairReview.side_no B T u e.2 ht hu]; exact hBs false
  have hyes : Disj T (yes B ((leaves u).contains ·)) A := by
    rw [←FreshPairReview.side_yes B T u e.2 ht hu]
    exact FreshPairReview.actual_clear_disj T _ _ (hClear.2 true)
  have hno : Disj T (no B ((leaves u).contains ·)) A := by
    rw [←FreshPairReview.side_no B T u e.2 ht hu]
    exact FreshPairReview.actual_clear_disj T _ _ (hClear.2 false)
  have hAin : A ∈ F' := List.count_pos_iff.mp (by omega)
  exact ⟨u,F',o,hu,rfl,hAF,hRef,hLen,ho,⟨hFQ,hQRef,hQ.1,hQ.2,hReal,hBudget⟩,
    side_output_clear S T A B C (leaves u) q o ho hp hyes hno,
    kept_parent_of_refinement S T A B C F' o.partition hp hAin hFQ hQRef hgood,
    side_input_color_count S T A B C (leaves u) hp ht hl hBy hBn,
    side_raw_mass S T A B C (leaves u) hp ht hl hBy hBn q c hc⟩
end Universal233.PairAssembly
