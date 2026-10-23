import VertexPair

namespace Universal233.PairAssembly
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PaidAssembly

theorem restriction_agrees_swap (S T : Tree) (L : List Nat)
    (h : restrictionAgrees S T L = true) : restrictionAgrees T S L = true := by
  unfold restrictionAgrees at h ⊢
  cases hS : restrict L S <;> cases hT : restrict L T <;> simp only [hS,hT] at h ⊢
  all_goals try contradiction
  exact (sameShape_correct _ _).2 (iso_symm ((sameShape_correct _ _).1 h))

theorem agreement_swap (S T : Tree) (F : List (List Nat)) (h : agreement S T F = true) :
    agreement T S F = true := by
  simp only [agreement,Bool.and_eq_true] at h ⊢
  refine ⟨⟨⟨⟨h.1.1.1.2,h.1.1.1.1⟩,?_⟩,h.2⟩,h.1.2⟩
  apply List.all_eq_true.2
  intro L hL
  exact restriction_agrees_swap S T L (List.all_eq_true.1 h.1.1.2 L hL)

theorem proper_pair_from_partition (S T : Tree) (A B C : List Nat)
    (ht : (leaves T).Nodup) (hl : ∀ x, x ∈ leaves S → x ∈ leaves T)
    (hp : partitionCheck (leaves S) [A,B,C] = true) : PairGeometry.properInput T A B = true := by
  obtain ⟨hab,_,_⟩ := Assembly.parent_partition_disjoint S A B C hp
  have hnA := parent_nodup (leaves S) [A,B,C] hp A (by simp)
  have hnB := parent_nodup (leaves S) [A,B,C] hp B (by simp)
  have hneA := partitionCheck_nonempty _ _ hp A (by simp)
  have hneB := partitionCheck_nonempty _ _ hp B (by simp)
  simp only [PairGeometry.properInput,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',isEmpty_false]
  refine ⟨⟨⟨⟨⟨⟨⟨ht,hnA⟩,hnB⟩,hneA⟩,hneB⟩,?_⟩,?_⟩,?_⟩
  · apply List.all_eq_true.2
    intro x hx
    exact List.contains_iff_mem.2 (hl x (partitionCheck_subset _ [A,B,C] hp (by simp [hx])))
  · apply List.all_eq_true.2
    intro x hx
    exact List.contains_iff_mem.2 (hl x (partitionCheck_subset _ [A,B,C] hp (by simp [hx])))
  · apply List.all_eq_true.2
    intro x hx
    simpa using (show x ∉ B from fun hb => hab x hx hb)

def goodPairOutputs (S T : Tree) (A B : List Nat) (q : Nat) : List Output :=
  match PairGeometry.choose T A B with
  | some (.vertex v) => vertexPairOutputs S T A B v q
  | some (.edge e) => sideOutputs S A B (PairGeometry.descendants T e.2) q
  | none => []

def ChoiceProgress (S T : Tree) (A B : List Nat) (o : Output) : PairGeometry.Choice → Prop
  | .vertex v => VertexPairClearing T o.partition A B v
  | .edge _ => (∀ K, K ∈ o.partition → Sub K B → Disj T K A) ∧
      ∃ K, K ∈ o.partition ∧ (∀ x, x ∈ K ↔ x ∈ A) ∧ restrictionAgrees S T K = true

/-- The actual edge-descendant list and the restricted-subtree leaf list give
identical concrete colors. No display edge is used for source charging. -/
theorem side_outputs_descendant (S T u : Tree) (A B : List Nat) (v : RMAF.Vertex)
    (ht : (leaves T).Nodup) (hu : treeAt T v = some u) (q : Nat) :
    sideOutputs S A B (PairGeometry.descendants T v) q = sideOutputs S A B (leaves u) q := by
  have he : sideColor (PairGeometry.descendants T v) = sideColor (leaves u) := by
    funext x
    have hx := FreshPairReview.descendants_treeAt T u v ht hu x
    simp only [sideColor,hx]
  simp only [sideOutputs,he]

/-- Total executable good-parent pair case at original-label hypotheses. The
choice is computed without F; an edge uses the exchange only in the proof. -/
theorem good_pair_cover_mass (S T : Tree) (A B C : List Nat) (F : List (List Nat)) (q : Nat)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (sameLabels : ∀ x, x ∈ leaves S ↔ x ∈ leaves T)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hsource : pairwiseEmbeddings S [A,B,C] = true) (hAB : A ≠ B)
    (hover : ∃ v, v ∈ minimalVertices A T ∧ v ∈ minimalVertices B T)
    (clearOther : ∀ E, E ∈ [A,B,C] → E ≠ A → E ≠ B → Disj T E A ∧ Disj T E B)
    (hgood : restrictionAgrees S T A = true)
    (hF : agreement S T F = true) (hFP : RefinesBlocks F [A,B,C]) (hq : F.length-1 ≤ q)
    (c : Rat) (hc : 2 ≤ c) :
    (∃ F' o choice, PairGeometry.choose T A B = some choice ∧
      agreement S T F' = true ∧ F'.length ≤ F.length ∧ RefinesBlocks F' [A,B,C] ∧
      o ∈ goodPairOutputs S T A B q ∧ OutputWitness S [A,B,C] F' q o ∧
      ChoiceProgress S T A B o choice) ∧
    rawQMass c (goodPairOutputs S T A B q) ≤ c^(-3 : Int)+c^(-4 : Int) := by
  have hl : ∀ x, x ∈ leaves S → x ∈ leaves T := fun x hx => (sameLabels x).1 hx
  have hproper := proper_pair_from_partition S T A B C ht hl hp
  obtain ⟨choice,hchoose,hvalid⟩ := PairGeometry.choose_complete T A B hproper hover
  cases choice with
  | vertex v =>
    obtain ⟨hA,hB,hthree⟩ := hvalid
    obtain ⟨o,ho,hOut,hclear⟩ := vertex_pair_cover T S A B C F v q ht hs hl
      (agreement_swap S T F hF) hp hFP hA hB hq
    have hm := vertex_pair_three_mass S T A B C v ht hl hp hA hB hthree q c hc
    refine ⟨⟨F,o,.vertex v,hchoose,hF,Nat.le_refl _,hFP,?_,hOut,hclear⟩,?_⟩
    · simpa only [goodPairOutputs,hchoose] using ho
    · simpa only [goodPairOutputs,hchoose] using hm
  | edge e =>
    obtain ⟨u,F',o,hu,heq,hAF,hRef,hLen,ho,hOut,hClear,hKept,_,hMass⟩ :=
      selected_edge_good_parent_core S T A B C e F q hs sameLabels hp hsource hAB hchoose
        clearOther hgood hF hFP hq c hc
    have he := side_outputs_descendant S T u A B e.2 ht hu q
    have hm : rawQMass c (goodPairOutputs S T A B q) ≤ c^(-3 : Int) := by
      simpa only [goodPairOutputs,hchoose,he] using hMass
    have hpos : 0 ≤ c^(-4 : Int) := by
      change 0 ≤ (c^4)⁻¹
      exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.pow_pos (by grind)))
    refine ⟨⟨F',o,.edge e,hchoose,hAF,hLen,hRef,?_,hOut,⟨hClear,hKept⟩⟩,?_⟩
    · simpa only [goodPairOutputs,hchoose,he] using ho
    · grind
end Universal233.PairAssembly
