import PlannerFacts
namespace Universal233.BothBad
open RMAF CoreProgram SourceCoverage PairAssembly BinaryCheap RankConsumer

theorem cheapPlan_sources (S T : Tree) (A B C D : List Nat) (q : Nat)
    (cheap opposite : List Output) (e : Entry) (he : e∈cheapPlan S T A B C D q cheap opposite) :
    e.output∈cheap ∨ e.output∈opposite := by
  by_cases hg : (restrictionAgrees S T (ay A D) && restrictionAgrees S T (an A D))=true
  · simp only [cheapPlan,hg,ite_true] at he
    cases hk : knownOne T S A with
    | none => simp [hk] at he
    | some F =>
      simp only [hk,List.mem_append] at he
      rcases he with ha | hb
      · exact Or.inl (entries_sound q .ordinary cheap e ha).1
      · exact Or.inr (entries_sound q (.retained A B C F) opposite e hb).1
  · simp only [cheapPlan,hg,ite_false] at he
    rcases List.mem_append.1 he with ha | hb
    · exact Or.inl (entries_sound q .ordinary cheap e ha).1
    · exact Or.inr (entries_sound q .full opposite e hb).1

theorem plan_sources (S T : Tree) (A B C : List Nat) (edge : RMAF.Vertex × RMAF.Vertex)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (hl : ∀ x, x∈leaves S → x∈leaves T)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (hchoose : PairGeometry.choose T A B=some (.edge edge))
    (q : Nat) (e : Entry) (he : e∈plan S T A B C (PairGeometry.descendants T edge.2) q) :
    e.output∈outputs S A B (PairGeometry.descendants T edge.2) q := by
  let D := PairGeometry.descendants T edge.2
  have hD : D=PairGeometry.descendants T edge.2 := rfl
  obtain ⟨u,hu,hyA,hnA,hyB,hnB,_⟩ := edge_facts T A B edge hchoose
  have hd : ∀ U, ay U D=ay U (leaves u) ∧ an U D=an U (leaves u) := by
    intro U
    exact ⟨FreshPairReview.side_yes U T u edge.2 ht hu,FreshPairReview.side_no U T u edge.2 ht hu⟩
  have hrA : RankDichotomy.inputRank S (cheapColor A B D)=4 :=
    cheap_rank S T A B C D hp ht hl (by rw [(hd A).1];exact hyA) (by rw [(hd A).2];exact hnA)
  have hrB : RankDichotomy.inputRank S (cheapColor B A D)=4 :=
    cheap_rank S T B A C D (partition_swap _ A B C hp) ht hl
      (by rw [(hd B).1];exact hyB) (by rw [(hd B).2];exact hnB)
  change e∈plan S T A B C D q at he
  change e.output∈outputs S A B D q
  unfold plan at he
  split at he
  · simp at he
  · rename_i hq
    have haExact := reuse_exact S (cheapColor A B D) hs hrA q (by omega)
    have hbExact := reuse_exact S (cheapColor B A D) hs hrB q (by omega)
    by_cases ha : (fourProbe S (cheapColor A B D)).outputs.isEmpty
    · by_cases hb : (fourProbe S (cheapColor B A D)).outputs.isEmpty
      · simp only [ha,hb,ite_true] at he
        exact (entries_sound q .full _ e he).1
      · simp only [ha,hb,ite_true,ite_false] at he
        have hsources := cheapPlan_sources S T B A C D q _ _ e he
        have heB : (fourProbe S (cheapColor B A D)).outputs=(generate S (cheapColor B A D) q).outputs := by
          simpa [reuse,hb] using hbExact
        rcases hsources with hB | hA
        · have hh : e.output∈(generate S (cheapColor B A D) q).outputs := by rw [←heB];exact hB
          exact List.mem_append.2 (Or.inr hh)
        · rw [haExact] at hA
          exact List.mem_append.2 (Or.inl hA)
    · simp only [ha,ite_false] at he
      have hsources := cheapPlan_sources S T A B C D q _ _ e he
      have heA : (fourProbe S (cheapColor A B D)).outputs=(generate S (cheapColor A B D) q).outputs := by
        simpa [reuse,ha] using haExact
      rcases hsources with hA | hB
      · have hh : e.output∈(generate S (cheapColor A B D) q).outputs := by rw [←heA];exact hA
        exact List.mem_append.2 (Or.inl hh)
      · rw [hbExact] at hB
        exact List.mem_append.2 (Or.inr hB)
end Universal233.BothBad
