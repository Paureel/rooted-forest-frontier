import Continuation
namespace Universal233.BinaryCheap
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly RankDichotomy RankConsumer

theorem sector_count (A D : List Nat) (x : Nat) :
    (ay A D).count x+(an A D).count x = A.count x := by
  induction A with
  | nil => simp [ay,an,yes,no]
  | cons a A ih =>
    by_cases hd : a ∈ D <;> simp [ay,an,yes,no,hd,List.count_cons] at ih ⊢ <;> omega

theorem classes_partition (S : Tree) (A B C D : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hy : ay A D ≠ []) (hn : an A D ≠ []) :
    partitionCheck (leaves S) (classes A B C D) = true := by
  apply partition_intro
  · exact classes_nonempty S A B C D hp hy hn
  · intro x hx
    have hcount := (partition_parts _ _ hp).2.1 x hx
    have hsector := sector_count A D x
    simp only [classes,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append] at hcount ⊢
    omega
  · intro x hx
    obtain ⟨K,hK,hxK⟩ := List.mem_flatten.1 hx
    exact classes_member_source S A B C D K hp hK x hxK

theorem sectors_source (S : Tree) (A B C D : List Nat) (o : Output)
    (hs : (leaves S).Nodup)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hy : ay A D ≠ []) (hn : an A D ≠ [])
    (ho : pairwiseEmbeddings S o.partition = true)
    (hex : ∀ L, L ∈ classes A B C D → ∃ K, K ∈ o.partition ∧ SameMembers K L) :
    Disj S (ay A D) (an A D) := by
  have hpart := classes_partition S A B C D hp hy hn
  have hflat := (Universal233.DepthOne.checked_flatten_perm (leaves S) _ hs hpart).nodup_iff.2 hs
  have hmap : ∀ L, L ∈ classes A B C D → ∃ K, K ∈ o.partition ∧ SameMembers L K := by
    intro L hL
    obtain ⟨K,hK,hKL⟩ := hex L hL
    exact ⟨K,hK,fun x => (hKL x).symm⟩
  have hpw := pairwise_members S (classes A B C D) o.partition hflat
    (classes_nonempty S A B C D hp hy hn) hmap ((executable_pairwiseEmbeddings S _).1 ho)
  exact (List.pairwise_cons.1 hpw).1 _ (by simp [classes])

theorem local_sectors_partition (S s : Tree) (A B C D : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hr : restrict A S = some s) (hy : ay A D ≠ []) (hn : an A D ≠ []) :
    partitionCheck (leaves s) [ay A D,an A D] = true := by
  have hAn : A.Nodup := parent_nodup (leaves S) [A,B,C] hp A (by simp)
  apply partition_intro
  · intro L hL
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
    rcases hL with rfl | rfl
    · exact hy
    · exact hn
  · intro x hx
    have hxa := ((RestrictionBridge.restricted_labels_exact S s A hr).1 hx).2
    have hc := sector_count A D x
    simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append]
    rw [hc,hAn.count]
    simp [hxa]
  · intro x hx
    have hxa : x ∈ A := by
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append] at hx
      rcases hx with hx | hx <;> exact (List.mem_filter.1 hx).1
    exact (RestrictionBridge.restricted_labels_exact S s A hr).2
      ⟨(parent_cover S A B C hp x).2 (Or.inl hxa),hxa⟩

/-- Both good cheap sectors give a literal two-piece agreement on the exact
original restricted local trees. No union of display source cuts is used. -/
theorem local_cost_one (S T : Tree) (A B C D : List Nat) (o : Output)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x ∈ leaves S ↔ x ∈ leaves T)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hy : ay A D ≠ []) (hn : an A D ≠ [])
    (ho : pairwiseEmbeddings S o.partition = true)
    (hex : ∀ L, L ∈ classes A B C D → ∃ K, K ∈ o.partition ∧ SameMembers K L)
    (hsector : Disj T (ay A D) (an A D))
    (hgoodY : restrictionAgrees S T (ay A D) = true)
    (hgoodN : restrictionAgrees S T (an A D) = true) :
    ∃ s t, restrict A S = some s ∧ restrict A T = some t ∧
      agreement t s [ay A D,an A D] = true ∧
      Universal233.DepthOne.proper t s = true := by
  obtain ⟨x,hx⟩ := nonempty_witness A (partitionCheck_nonempty _ _ hp A (by simp))
  have hxs := (parent_cover S A B C hp x).2 (Or.inl hx)
  obtain ⟨s,hrs⟩ := RestrictionBridge.restriction_exists S A ⟨x,hxs,hx⟩
  obtain ⟨t,hrt⟩ := RestrictionBridge.restriction_exists T A ⟨x,(same x).1 hxs,hx⟩
  have hlabels : ∀ x, x ∈ leaves t ↔ x ∈ leaves s := by
    intro x
    rw [RestrictionBridge.restricted_labels_exact T t A hrt,RestrictionBridge.restricted_labels_exact S s A hrs,same x]
  have hsn := RestrictionBridge.restricted_nodup S s A hrs hs
  have htn := RestrictionBridge.restricted_nodup T t A hrt ht
  have hproper : Universal233.DepthOne.proper t s = true :=
    Universal233.DepthOne.proper_iff t s |>.2 ⟨htn,hsn,(List.perm_ext_iff_of_nodup htn hsn).2 hlabels⟩
  have hps := local_sectors_partition S s A B C D hp hrs hy hn
  have hpt : partitionCheck (leaves t) [ay A D,an A D] = true := by
    have he : (leaves s).Perm (leaves t) := (List.perm_ext_iff_of_nodup hsn htn).2 (fun x => (hlabels x).symm)
    have hc : ∀ x, (leaves s).contains x = (leaves t).contains x := by
      intro x; apply Bool.eq_iff_iff.2; simpa only [List.contains_iff_mem] using (hlabels x).symm
    simpa only [partitionCheck,he.all_eq,hc] using hps
  have hsub : ∀ L, L ∈ [ay A D,an A D] → L ⊆ A := by
    intro L hL
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
    rcases hL with rfl | rfl <;> intro x hx <;> exact (List.mem_filter.1 hx).1
  have hsrc : pairwiseEmbeddings s [ay A D,an A D] = true := by
    apply (RestrictionBridge.pairwise_transport S s A _ hrs hsub).1
    have hc := (executable_disjointVertices S _ _).2 (sectors_source S A B C D o hs hp hy hn ho hex)
    simpa [pairwiseEmbeddings] using hc
  have htgt : pairwiseEmbeddings t [ay A D,an A D] = true := by
    apply (RestrictionBridge.pairwise_transport T t A _ hrt hsub).1
    have hc := (executable_disjointVertices T _ _).2 hsector
    simpa [pairwiseEmbeddings] using hc
  have hgood : ∀ L, L ∈ [ay A D,an A D] → restrictionAgrees s t L = true := by
    intro L hL
    rw [RestrictionBridge.sameShape_restrict_inside S T s t A L hrs hrt (hsub L hL)]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
    rcases hL with rfl | rfl
    · exact hgoodY
    · exact hgoodN
  have hagree : agreement s t [ay A D,an A D] = true := by
    simp only [agreement,Bool.and_eq_true,List.all_eq_true]
    exact ⟨⟨⟨⟨hps,hpt⟩,hgood⟩,hsrc⟩,htgt⟩
  exact ⟨s,t,hrs,hrt,agreement_swap s t _ hagree,hproper⟩
end Universal233.BinaryCheap
