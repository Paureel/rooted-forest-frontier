import TargetGeometry
namespace Universal233.BinaryCheap
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly RankDichotomy RankConsumer

/-- Every actual opposite-core output keeps the same original A/C and supplied
literal local certificate. B pieces may overlap one another; cross-group
clearance is proved for their actual target embeddings. -/
theorem every_opposite_output (S T : Tree) (A B C D : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hsource : pairwiseEmbeddings S [A,B,C] = true)
    (hyes : Disj T (ay B D) A) (hno : Disj T (an B D) A)
    (hac : Disj T A C) (hbc : Disj T B C)
    (a : Output) (ha : KeptParent.OriginalLocalOneCut S T A a)
    (q : Nat) (o : Output) (ho : o ∈ sideOutputs S A B D q) :
    KeptParent.Keeps A o ∧ KeptParent.Keeps C o ∧
    (∃ K, K ∈ o.partition ∧ SameMembers K A ∧
      restrict K S = restrict A S ∧ restrict K T = restrict A T ∧
      KeptParent.OriginalLocalOneCut S T K a) ∧
    (∀ L, L ∈ o.partition → Sub L B → Disj T L A ∧ Disj T L C) ∧
    Disj T A C := by
  have hkept := KeptParent.generated_keeps_A_C S A B C (sideColor D) hp hsource q o ho
  obtain ⟨K,hK,hKA,hcert⟩ := KeptParent.every_output_retains_original_local_cut S T A B C
    (sideColor D) hp hsource a ha q o ho
  refine ⟨hkept.1,hkept.2,⟨K,hK,hKA,KeptParent.restrict_same_members K A hKA S,
    KeptParent.restrict_same_members K A hKA T,hcert⟩,?_,hac⟩
  intro L hL hLB
  exact ⟨side_output_clear S T A B C D q o ho hp hyes hno L hL hLB,
    disj_mono hbc hLB (fun _ h => h)⟩

/-- The alternative branch has two actual bad ordinary components in the
literal cheap output. Its premises/conclusion do not infer a paid query from
positive own optimum. A solver's explicit two-component guard can consume it. -/
theorem cheap_two_bad (S T : Tree) (A B C D : List Nat) (o : Output)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hB : restrictionAgrees S T B = false)
    (hy : ay A D ≠ []) (hn : an A D ≠ [])
    (hbad : restrictionAgrees S T (ay A D) = false ∨ restrictionAgrees S T (an A D) = false)
    (hclearY : Disj T (ay A D) B) (hclearN : Disj T (an A D) B)
    (hex : ∀ L, L ∈ classes A B C D → ∃ K, K ∈ o.partition ∧ SameMembers K L) :
    ∃ K L, K ∈ o.partition ∧ L ∈ o.partition ∧ K ≠ L ∧
      restrictionAgrees S T K = false ∧ restrictionAgrees S T L = false ∧ Disj T K L := by
  obtain ⟨KB,hKB,hKBB⟩ := hex B (by simp [classes])
  obtain ⟨hab,hac,hbc⟩ := Assembly.parent_partition_disjoint S A B C hp
  have finish : ∀ U, (U = ay A D ∨ U = an A D) → restrictionAgrees S T U = false →
      Disj T U B → U ≠ [] →
      ∃ K L, K ∈ o.partition ∧ L ∈ o.partition ∧ K ≠ L ∧
        restrictionAgrees S T K = false ∧ restrictionAgrees S T L = false ∧ Disj T K L := by
    intro U hU hu hclear hne
    obtain ⟨K,hK,hKU⟩ := hex U (by rcases hU with rfl | rfl <;> simp [classes])
    have hUA : Sub U A := by rcases hU with rfl | rfl <;> intro x hx <;> exact (List.mem_filter.1 hx).1
    have hneq : K ≠ KB := by
      intro he
      obtain ⟨x,hx⟩ := nonempty_witness U hne
      exact hab x (hUA x hx) ((hKBB x).1 (he ▸ (hKU x).2 hx))
    exact ⟨K,KB,hK,hKB,hneq,(KeptParent.restriction_agrees_same_members S T K U hKU).trans hu,
      (KeptParent.restriction_agrees_same_members S T KB B hKBB).trans hB,
      disj_mono hclear (fun x hx => (hKU x).1 hx) (fun x hx => (hKBB x).1 hx)⟩
  rcases hbad with hb | hb
  · exact finish _ (Or.inl rfl) hb hclearY hy
  · exact finish _ (Or.inr rfl) hb hclearN hn

/-- Both actual q3 failures force every actual output cost>=4 and bind the
same appended raw output list to the combined 4*c^-4 bound. -/
theorem two_high (S T : Tree) (A B C D : List Nat)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hay : ay A D ≠ []) (han : an A D ≠ []) (hby : ay B D ≠ []) (hbn : an B D ≠ [])
    (hA : fourAccepted S (cheapColor A B D) = false)
    (hB : fourAccepted S (cheapColor B A D) = false)
    (q : Nat) (c : Rat) (hc : 2 ≤ c) :
    (∀ o, o ∈ sideOutputs S B A D q ++ sideOutputs S A B D q → 4 ≤ o.sourceCuts.length) ∧
    rawQMass c (sideOutputs S B A D q ++ sideOutputs S A B D q) ≤ 4*c^(-4 : Int) := by
  have hrA := cheap_rank S T A B C D hp ht hl hay han
  have hrB := cheap_rank S T B A C D (partition_swap _ A B C hp) ht hl hby hbn
  have hAhigh := four_rejected_high S (cheapColor A B D) hs hrA hA q c hc
  have hBhigh := four_rejected_high S (cheapColor B A D) hs hrB hB q c hc
  constructor
  · intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact hAhigh.1 o ho
    · exact hBhigh.1 o ho
  · have hadd : rawQMass c (sideOutputs S B A D q ++ sideOutputs S A B D q) =
        rawQMass c (sideOutputs S B A D q)+rawQMass c (sideOutputs S A B D q) := by simp [rawQMass,List.map_append,List.sum_append]
    rw [hadd]
    have h1 : rawQMass c (sideOutputs S B A D q) ≤ 2*c^(-4 : Int) := hAhigh.2
    have h2 : rawQMass c (sideOutputs S A B D q) ≤ 2*c^(-4 : Int) := hBhigh.2
    grind
end Universal233.BinaryCheap
