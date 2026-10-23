import LocalOne
namespace Universal233.BinaryCheap
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly RankDichotomy RankConsumer

theorem local_pretest_one (S T : Tree) (A : List Nat)
    (hbad : restrictionAgrees S T A = false)
    (s t : Tree) (hrs : restrict A S = some s) (hrt : restrict A T = some t)
    (hp : DepthOne.proper t s = true)
    (F : List (List Nat)) (hF : agreement t s F = true) (hcost : F.length = 2) :
    ∃ p, DepthOne.pretest01 t s = .found (some p) ∧
      KeptParent.OriginalLocalOneCut S T A ⟨DepthOne.forest s (some p),[p]⟩ ∧
      (∀ H, agreement t s H = true → 1 ≤ H.length-1) := by
  obtain ⟨cut,hfound,hagree,hbound⟩ := DepthOne.pretest_complete t s hp F hF (by omega)
  have hminimum := DepthOne.found_original_minimum t s cut hfound
  cases cut with
  | none =>
    have hs := hagree
    simp only [agreement,Bool.and_eq_true,DepthOne.forest,List.all_cons,List.all_nil,Bool.and_true] at hs
    have hsame := hs.1.1.2
    have hss : restrict (leaves s) s = some s := restrict_of_contains s _ (by intro x hx; simpa using hx)
    have hts : restrict (leaves s) t = some t := by
      apply restrict_of_contains
      intro x hx
      exact List.contains_iff_mem.2 (((DepthOne.proper_iff t s).1 hp).2.2.mem_iff.1 hx)
    have htshape : sameShape t s = true := by simpa only [restrictionAgrees,hts,hss] using hsame
    have hstshape : sameShape s t = true := (sameShape_correct s t).2 (iso_symm ((sameShape_correct t s).1 htshape))
    have horiginal : restrictionAgrees S T A = true := by simp only [restrictionAgrees,hrs,hrt,hstshape]
    simp [hbad] at horiginal
  | some p =>
    have hc : (DepthOne.sourceCuts (some p)).length = 1 := rfl
    refine ⟨p,hfound,⟨s,t,hrs,hrt,hminimum.2.1,agreement_swap t s _ hagree,hc⟩,?_⟩
    intro H hH
    exact hminimum.2.2.2.2 H hH

/-- A bad A plus both good cheap sectors forces the actual DepthOne pretest
on its original local restricted trees to return a globally minimum one-cut
certificate. This is derived from the actual cheap output's source embeddings. -/
theorem cheap_good_sectors_pretest (S T : Tree) (A B C D : List Nat) (o : Output)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x ∈ leaves S ↔ x ∈ leaves T)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hbad : restrictionAgrees S T A = false)
    (hy : ay A D ≠ []) (hn : an A D ≠ [])
    (ho : pairwiseEmbeddings S o.partition = true)
    (hex : ∀ L, L ∈ classes A B C D → ∃ K, K ∈ o.partition ∧ SameMembers K L)
    (hsector : Disj T (ay A D) (an A D))
    (hgoodY : restrictionAgrees S T (ay A D) = true)
    (hgoodN : restrictionAgrees S T (an A D) = true) :
    ∃ s t p, restrict A S = some s ∧ restrict A T = some t ∧
      DepthOne.pretest01 t s = .found (some p) ∧
      KeptParent.OriginalLocalOneCut S T A ⟨DepthOne.forest s (some p),[p]⟩ ∧
      (∀ H, agreement t s H = true → 1 ≤ H.length-1) := by
  obtain ⟨s,t,hrs,hrt,hagree,hproper⟩ := local_cost_one S T A B C D o hs ht same hp hy hn ho hex hsector hgoodY hgoodN
  obtain ⟨p,hfound,hcert,hmin⟩ := local_pretest_one S T A hbad s t hrs hrt hproper [ay A D,an A D] hagree rfl
  exact ⟨s,t,p,hrs,hrt,hfound,hcert,hmin⟩
end Universal233.BinaryCheap
